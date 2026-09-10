import { readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import process from 'node:process';

const SKIP_DIRS = new Set(['node_modules', 'vendor']);

function collectJsFiles(dir) {
  const out = [];
  for (const entry of readdirSync(dir)) {
    if (SKIP_DIRS.has(entry)) continue;
    const full = join(dir, entry);
    const stat = statSync(full);
    if (stat.isDirectory()) {
      out.push(...collectJsFiles(full));
    } else if (entry.endsWith('.js')) {
      out.push(full);
    }
  }
  return out;
}

const files = collectJsFiles('.');
const failures = [];

for (const file of files) {
  try {
    execFileSync(process.execPath, ['--check', file], { stdio: 'pipe' });
  } catch (err) {
    failures.push({ file, message: err.stderr?.toString() ?? err.message });
  }
}

if (failures.length > 0) {
  for (const { file, message } of failures) {
    console.error(`✗ ${file}`);
    console.error(message);
  }
  console.error(`\n${failures.length} file(s) failed syntax check.`);
  process.exitCode = 1;
} else {
  console.log(`✓ ${files.length} file(s) passed syntax check.`);
}
