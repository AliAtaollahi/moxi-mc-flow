import json
import pathlib
import sys
import threading

from src import moxi, parse_moxi, log

FILE_NAME = pathlib.Path(__file__).name

# `Program.to_json` and `json.dump` both walk the term tree recursively, and
# with `let` bindings that tree is as deep as the binding chain is long -- tens
# of thousands of levels on a model that came out of a large transition system.
# Raising `sys.setrecursionlimit` on its own segfaults, since the limit is only
# a counter and the real constraint is the C stack, so the walk runs on a
# thread with a stack big enough to hold the frames.
RECURSION_LIMIT = 300_000
STACK_SIZE = 512 * 1024 * 1024


def write_json(program: moxi.Program, output_path: pathlib.Path, do_pretty: bool) -> int:
    result: list[int] = []

    def dump() -> None:
        try:
            with open(output_path, "w") as f:
                json.dump(program.to_json(), f, indent=4 if do_pretty else None)
            result.append(0)
        except RecursionError:
            log.error("Term tree too deep to serialize", FILE_NAME)
            result.append(1)

    limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(limit, RECURSION_LIMIT))

    try:
        threading.stack_size(STACK_SIZE)
    except (ValueError, RuntimeError):
        log.debug(1, "Could not enlarge the thread stack", FILE_NAME)

    thread = threading.Thread(target=dump)
    thread.start()
    thread.join()

    sys.setrecursionlimit(limit)

    return result[0] if result else 1


def main(
    input_path: pathlib.Path, output_path: pathlib.Path, do_sort_check: bool, do_pretty: bool = True
) -> int:
    if not input_path.is_file():
        log.error(f"'{input_path}' is not a valid file.", FILE_NAME)
        return 1

    if output_path.exists():
        log.error(f"Output path '{output_path}' already exists.", FILE_NAME)
        return 1

    program = parse_moxi.parse(input_path)

    if not program:
        log.error("Failed parsing\n", FILE_NAME)
        return 1

    if do_sort_check:
        (well_sorted, _) = moxi.sort_check(program)
        if not well_sorted:
            log.error("Failed sort check\n", FILE_NAME)
            return 2

    return write_json(program, output_path, do_pretty)
