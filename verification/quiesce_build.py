#!/usr/bin/env python3
"""Stop only a completed build's remaining process group before caching files."""
from pathlib import Path
import json
import os
import signal
import subprocess
import time


def members(group):
    table = subprocess.check_output(['ps', '-eo', 'pid=,pgid=,stat='], text=True)
    result = []
    for line in table.splitlines():
        pid, pgid, state = line.split()
        if int(pgid) == group and not state.startswith('Z'):
            result.append(int(pid))
    return result


def main():
    record = Path('.scratch/ci-build-process-group.json')
    if not record.exists():
        print('No build process group was started.')
        return
    data = json.loads(record.read_text())
    group = data['process_group']
    if not isinstance(group, int) or group <= 1 or group == os.getpgrp():
        raise RuntimeError('Invalid recorded build process group')
    if Path(data['working_directory']).resolve() != Path.cwd().resolve():
        raise RuntimeError('Recorded build belongs to a different project')
    for signum in [signal.SIGTERM, signal.SIGKILL]:
        active = members(group)
        if not active:
            print('Build process group is quiescent; cache files have no remaining compiler writers.')
            return
        print('Stopping remaining build process IDs:', ', '.join(map(str, active)), flush=True)
        try:
            os.killpg(group, signum)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            if not members(group):
                print('Build process group is quiescent; completed artifacts may now be archived.')
                return
            time.sleep(0.1)
    raise RuntimeError('Build processes remain active; do not archive changing proof artifacts')


if __name__ == '__main__':
    main()
