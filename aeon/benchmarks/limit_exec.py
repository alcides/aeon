"""Internal POSIX exec wrapper used by the benchmark storage policy."""

import os
import resource
import sys


def main():
    limit = int(sys.argv[1])
    if limit <= 0 or len(sys.argv) < 3:
        raise SystemExit("Expected a positive file-size limit and a command")
    resource.setrlimit(resource.RLIMIT_FSIZE, (limit, limit))
    os.execvpe(sys.argv[2], sys.argv[2:], os.environ)


if __name__ == "__main__":
    main()
