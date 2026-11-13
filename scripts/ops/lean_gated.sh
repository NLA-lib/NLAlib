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
lock_path=$runtime_dir/nlalib-workers.lock
owner_fd=${NLALIB_OPS_GATE_OWNER_FD:-}
in_scope=false
# A wrapper such as audit.py can invoke the gate again. Its outer gate still owns the lock.
if [[ $owner_fd =~ ^/proc/[0-9]+/fd/[0-9]+$ && $owner_fd -ef $lock_path ]]; then
  in_scope=true
else
  exec {lock_fd}>>"$lock_path" || exit $?
  flock --exclusive "$lock_fd" || exit $?
fi

STAT=/sys/fs/cgroup/user.slice/user-$uid.slice/user@$uid.service/nlalib.slice/nlalib-workers.slice/memory.stat
LIMIT=$((6 * 1024 * 1024 * 1024))
while :; do
  anon=$(awk '$1=="anon"{print $2}' "$STAT" 2>/dev/null || echo 0)
  if ! pgrep -x lean >/dev/null && [ "${anon:-0}" -lt "$LIMIT" ]; then break; fi
  sleep 10
done
if "$in_scope"; then
  exec env LEAN_NUM_THREADS=2 "$@"
fi

# The gate holds the lock while systemd-run waits for the command. Close the
# descriptor in the child so its descendants cannot retain the lock.
systemd-run --user --scope --slice=nlalib-workers.slice -q env LEAN_NUM_THREADS=2 \
  NLALIB_OPS_GATE_OWNER_FD="/proc/$$/fd/$lock_fd" "$@" {lock_fd}>&-
exit $?
