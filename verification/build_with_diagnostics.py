#!/usr/bin/env python3
"""Retain full compiler output while keeping CI progress and stalls observable."""
from pathlib import Path
import argparse
import json
import os
import re
import signal
import subprocess
import sys
import threading
import time


def process_report(parent):
    try:
        table = subprocess.check_output(
            ['ps', '-eo', 'pid=,ppid=,stat=,pcpu=,rss=,etime=,args='], text=True)
        rows = []
        for line in table.splitlines():
            parts = line.strip().split(None, 6)
            if len(parts) == 7:
                rows.append(parts)
        family = {parent}
        while True:
            more = {int(row[0]) for row in rows if int(row[1]) in family}
            if more <= family:
                break
            family |= more
        selected = [row for row in rows if int(row[0]) in family]
        selected.sort(key=lambda row: int(row[4]), reverse=True)
        # Print only public proof filenames and resource counters, never the
        # command line or environment of another process on the runner.
        result = []
        for pid, ppid, state, cpu, rss, elapsed, args in selected[:12]:
            files = re.findall(r'([^\s/]+\.lean)(?=\s|$)', args)
            executable = Path(args.split(None, 1)[0]).name
            result.append(f'pid={pid} state={state} cpu={cpu}% rss={int(rss) // 1024}MiB '
                          f'elapsed={elapsed} executable={executable} proof={",".join(files) or "-"}')
        if Path('/proc/meminfo').exists():
            memory = Path('/proc/meminfo').read_text()
            for key in ['MemAvailable', 'SwapFree']:
                match = re.search(r'^' + key + r':\s+(\d+) kB', memory, re.M)
                if match:
                    result.append(f'{key}={int(match[1]) // 1024}MiB')
        return result
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        return ['Resource report unavailable: ' + str(error)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--interval', type=float, default=60)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command and command[0] == '--':
        command = command[1:]
    if not command:
        command = ['lake', '-R', 'build']
    scratch = Path('.scratch')
    scratch.mkdir(exist_ok=True)
    last_output = [time.monotonic()]
    finished = threading.Event()
    lock = threading.Lock()
    with (scratch / 'ci-build.log').open('w') as full, (scratch / 'ci-build-resources.log').open('w') as resources:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, bufsize=1, start_new_session=True)
        (scratch / 'ci-build-process-group.json').write_text(json.dumps({
            'process_group': process.pid, 'working_directory': str(Path.cwd().resolve()),
        }) + '\n')

        def announce(message):
            with lock:
                print(message, flush=True)
                resources.write(message + '\n')
                resources.flush()

        def monitor():
            while not finished.wait(args.interval):
                quiet = int(time.monotonic() - last_output[0])
                announce(f'CI heartbeat {time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime())}: '
                         f'compiler quiet for {quiet}s')
                for line in process_report(process.pid):
                    announce('  ' + line)

        def terminate(signum, frame):
            try:
                os.killpg(process.pid, signum)
            except ProcessLookupError:
                pass

        signal.signal(signal.SIGTERM, terminate)
        signal.signal(signal.SIGINT, terminate)
        thread = threading.Thread(target=monitor, daemon=True)
        thread.start()
        for line in process.stdout:
            last_output[0] = time.monotonic()
            full.write(line)
            full.flush()
            plain = re.sub(r'\x1b\[[0-9;]*m', '', line).rstrip()
            if (re.search(r'\b(?:Built|Replayed|error|failed|failure)\b', plain, re.I)
                    or plain.startswith(('Build completed', 'All targets', 'Running', 'info:'))):
                with lock:
                    print(plain, flush=True)
        status = process.wait()
        finished.set()
        thread.join()
        print(f'Compiler exit status: {status}. Full diagnostics: .scratch/ci-build.log', flush=True)
        if status:
            print('Last full diagnostics:', flush=True)
            print('\n'.join((scratch / 'ci-build.log').read_text().splitlines()[-80:]), flush=True)
        return status if status >= 0 else 128 - status


if __name__ == '__main__':
    sys.exit(main())
