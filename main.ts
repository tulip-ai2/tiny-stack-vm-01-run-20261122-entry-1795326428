// make.fun tiny-stack-vm-01 entry: a stack VM for make.fun's tiny stack ISA v1,
// written from kit program/generator/subject/ISA.md and vm.mjs (the rule).
// For every instance <id> under MAKEFUN_INPUT_DIR it runs program.bin with
// input.bin and writes stdout.bin + exit.txt under MAKEFUN_OUTPUT_DIR/<id>.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// run(program, input) => { b: output bytes, e: exit code (a trap's code on a trap) }
function run(p, x) {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  let sp = 0;
  const C = new Int32Array(64); // call stack
  let csp = 0;
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0; // input position
  let pc = 0;
  let steps = 0;
  const fin = (e) => ({ b: out.slice(0, olen), e });
  for (;;) {
    if (steps === 1e6) return fin(10); // step limit
    if (pc < 0 || pc >= n) return fin(9); // pc outside the program
    const op = p[pc];
    if (!(op < 8 || (op > 15 && op < 31) || (op > 31 && op < 35) || (op > 47 && op < 53) || op === 64 || op === 65 || (op > 79 && op < 84)))
      return fin(5); // unknown opcode
    const im = op === 1 ? 1 : op === 2 ? 4 : op > 47 && op < 52 ? 2 : 0;
    if (pc + im >= n) return fin(9); // immediate cut off by the program's end
    steps++;
    const nx = pc + 1 + im; // address of the next instruction
    pc = nx;
    switch (op) {
      case 0: // HALT
        return fin(0);
      case 1: // PUSH8, sign-extended
        if (sp > 255) return fin(3);
        D[sp++] = p[nx - 1] << 24 >> 24;
        break;
      case 2: // PUSH32, little-endian signed
        if (sp > 255) return fin(3);
        D[sp++] = p[nx - 4] | p[nx - 3] << 8 | p[nx - 2] << 16 | p[nx - 1] << 24;
        break;
      case 3: // POP
        if (!sp) return fin(2);
        sp--;
        break;
      case 4: // DUP
        if (!sp) return fin(2);
        if (sp > 255) return fin(3);
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: { // SWAP
        if (sp < 2) return fin(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6: // OVER
        if (sp < 2) return fin(2);
        if (sp > 255) return fin(3);
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: { // ROT ( a b c -- b c a )
        if (sp < 3) return fin(2);
        const t = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = t;
        break;
      }
      // binary arithmetic / logic
      case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        if (sp < 2) return fin(2);
        const a = D[sp - 2];
        const b = D[sp - 1];
        sp -= 2;
        if (op > 18 && op < 23 && !b) return fin(4); // division by zero
        let r;
        switch (op) {
          case 16: r = a + b | 0; break; // ADD, wraps
          case 17: r = a - b | 0; break; // SUB
          case 18: r = Math.imul(a, b); break; // MUL, low 32 bits
          case 19: r = a === -2147483648 && b === -1 ? a : a / b | 0; break; // DIV
          case 20: r = b === -1 ? 0 : a % b | 0; break; // MOD, sign of a
          case 21: r = (a >>> 0) / (b >>> 0) | 0; break; // DIVU
          case 22: r = (a >>> 0) % (b >>> 0) | 0; break; // MODU
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break; // only the low 5 bits count
          case 29: r = a >> (b & 31); break; // arithmetic
          case 30: r = a >>> (b & 31); break; // logical
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = a >>> 0 < b >>> 0 ? 1 : 0;
        }
        D[sp++] = r;
        break;
      }
      case 23: // NEG
        if (!sp) return fin(2);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27: // NOT
        if (!sp) return fin(2);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 48: case 49: case 50: { // JMP, JZ, JNZ: 2-byte signed relative
        const r = (p[nx - 2] | p[nx - 1] << 8) << 16 >> 16;
        if (op === 48) pc = nx + r;
        else {
          if (!sp) return fin(2);
          const v = D[--sp];
          if (op === 49 ? !v : v) pc = nx + r;
        }
        break;
      }
      case 51: // CALL, 2-byte unsigned target
        if (csp > 63) return fin(7);
        C[csp++] = nx;
        pc = p[nx - 2] | p[nx - 1] << 8;
        break;
      case 52: // RET
        if (!csp) return fin(8);
        pc = C[--csp];
        break;
      case 64: { // LOAD
        if (!sp) return fin(2);
        const a = D[sp - 1];
        if (a >>> 0 > 255) return fin(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE ( v addr -- )
        if (sp < 2) return fin(2);
        const a = D[sp - 1];
        if (a >>> 0 > 255) return fin(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 80: { // PRINT: decimal ASCII, a leading - when negative
        if (!sp) return fin(2);
        const s = '' + D[sp - 1];
        if (olen + s.length > 65536) return fin(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, v AND 255
        if (!sp) return fin(2);
        if (olen > 65535) return fin(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82: // IN: next input byte, -1 once used up
        if (sp > 255) return fin(3);
        D[sp++] = ip < x.length ? x[ip++] : -1;
        break;
      case 83: // EXIT with the low byte
        if (!sp) return fin(2);
        return fin(D[--sp] & 255);
    }
  }
}

for (const id of readdirSync(I)) {
  let prog;
  try {
    prog = readFileSync(join(I, id, 'program.bin'));
  } catch {
    continue; // not an instance directory
  }
  let inp = new Uint8Array(0);
  try {
    inp = readFileSync(join(I, id, 'input.bin'));
  } catch {}
  const { b, e } = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), b);
  writeFileSync(join(O, id, 'exit.txt'), e + '\n');
}
