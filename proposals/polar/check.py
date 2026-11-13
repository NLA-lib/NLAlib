"""Compile the standalone polar proposals against the current Lake environment."""
from graphlib import TopologicalSorter
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    directory = Path(__file__).resolve().parent
    root = directory.parents[1]
    modules = {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for path in directory.glob("*.lean")
    }
    if not modules:
        raise ValueError(f"No Lean proposals in {directory}")
    graph = TopologicalSorter()
    for module, path in modules.items():
        dependencies = []
        for line in path.read_text(encoding="utf-8").splitlines():
            words = line.removeprefix("public ").split()
            if words[:1] == ["import"]:
                dependencies.extend(name for name in words[1:] if name in modules)
        graph.add(module, *dependencies)

    with tempfile.TemporaryDirectory() as temp:
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join(filter(None, [temp, env.get("LEAN_PATH")]))
        for name in graph.static_order():
            source = modules[name]
            output = Path(temp) / source.relative_to(root).with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                ["lean", "--root", str(root), "-DwarningAsError=true",
                 "-o", str(output), str(source)],
                cwd=root, env=env, check=True,
            )
    print(f"Compiled {len(modules)} standalone polar proposal modules.")


if __name__ == "__main__":
    main()
