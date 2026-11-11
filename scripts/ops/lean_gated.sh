#!/usr/bin/env bash
# Run one Lean/lake command under the machine discipline of the builder brief:
# wait until no other `lean` process runs and the anonymous memory of
# nlalib-workers.slice is under 6 GB, then run it in that slice with two threads.
# Gated callers in all worktrees share one lock per user. Processes launched
# outside the gate are only covered by the checks before launch.
# Usage: scripts/ops/lean_gated.sh lake env lean NLAlib/Ops/Tools/Run.lean
set -u
uid=$(id -u)
runtime_dir=${XDG_RUNTIME_DIR:-/run/user/$uid}
exec {lock_fd}>>"$runtime_dir/nlalib-workers.lock" || exit $?
flock --exclusive "$lock_fd" || exit $?

STAT=/sys/fs/cgroup/user.slice/user-$uid.slice/user@$uid.service/nlalib.slice/nlalib-workers.slice/memory.stat
LIMIT=$((6 * 1024 * 1024 * 1024))
while :; do
  anon=$(awk '$1=="anon"{print $2}' "$STAT" 2>/dev/null || echo 0)
  if ! pgrep -x lean >/dev/null && [ "${anon:-0}" -lt "$LIMIT" ]; then break; fi
  sleep 10
done
# The gate holds the lock while systemd-run waits for the command. Close the
# descriptor in the child so its descendants cannot retain the lock.
systemd-run --user --scope --slice=nlalib-workers.slice -q env LEAN_NUM_THREADS=2 "$@" {lock_fd}>&-
exit $?
