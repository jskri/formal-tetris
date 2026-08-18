import { run } from 'node:test';
import { spec } from 'node:test/reporters';
import { readdirSync } from 'node:fs';
import { join } from 'node:path';
import process from 'node:process';

const dirs = ['t1', 't2', 't3', 't4', 't5', 't6', 't7'];
const files = dirs.flatMap((dir) => {
  const testdir = join(dir, 'tests');
  return readdirSync(testdir)
    .filter((f) => f.endsWith('.js'))
    .map((f) => join(testdir, f));
});

run({ files })
  .on('test:fail', () => { process.exitCode = 1; })
  .compose(new spec())
  .pipe(process.stdout);
