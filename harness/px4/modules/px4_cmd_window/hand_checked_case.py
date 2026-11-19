#!/usr/bin/env python3
"""The hand-checked case of px4_cmd_window (writes hand-checked-case.json next to this file).

405 ticks: commands at ticks 0 (2), 3 (1), 399 (4), 400 (1), 404 (3), none otherwise. The window
at tick k is the sum of the counts at ticks max(0, k-399)..k (adapter.cpp: the slot of tick k-400
leaves before tick k's count enters):
  ticks 0-2: 2; ticks 3-398: 3; tick 399: 7 (2 + 1 + 4, tick 0 still inside: 0..399);
  tick 400: 6 (tick 0 left: 1 + 4 + 1); ticks 401-402: 6; tick 403: 5 (tick 3 left);
  tick 404: 8 (5 + 3)."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'py'))
import px4_case  # noqa: E402

counts = {0: 2, 3: 1, 399: 4, 400: 1, 404: 3}
inputs = [{'vehicle_command_count': counts.get(k, 0)} for k in range(405)]
want = {k: (2 if k < 3 else 3 if k < 399 else 7 if k == 399 else 6 if k < 403 else
            5 if k == 403 else 8) for k in range(405)}
expect = {k: {'vehicle_command_last_400_ticks': v} for k, v in want.items()}
px4_case.record('px4_cmd_window', {}, inputs, expect, __doc__)
