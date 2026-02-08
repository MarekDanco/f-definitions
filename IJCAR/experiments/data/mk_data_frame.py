import pandas as pd
from pathlib import Path
import matplotlib.pyplot as plt

C_MAP = {
    "bench_600_40000": 1,
    "bench100_2000_40000": 2,
    "bench1000_2000_40000": 3,
    "bench10000_2000_40000": 4,
    "bench100000_2000_40000": 5,
}


def parse_tab(path, solver, c):
    rows = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or ";" not in line:
                continue

            parts = [p.strip() for p in line.split(";")]
            bench_path = parts[0]
            time_part = parts[1]
            status_part = parts[2]

            benchmark = Path(bench_path).stem

            time_tokens = time_part.split()
            time_s = int(time_tokens[0])

            if "s sat" in status_part:
                status = "sat"
            elif time_s >= 1800:
                status = "timeout"
            else:
                status = "unknown"

            rows.append(
                {
                    "c": c,
                    "solver": solver,
                    "benchmark": benchmark,
                    "time_s": time_s,
                    "status": status,
                }
            )
    return rows


base = Path("tables")
rows = []

for folder, c in C_MAP.items():
    for solver in ["cvc5", "z3"]:
        tab_file = base / folder / f"{solver}.tab"
        rows.extend(parse_tab(tab_file, solver, c))

df = pd.DataFrame(rows)
df["c"] = df["c"].astype(int)

solved = df[df["status"] == "sat"].groupby(["c", "solver"]).size().unstack(fill_value=0)
fig, ax = plt.subplots()
# Loop over each solver
for solver in solved.columns:
    marker = "^" if solver == "cvc5" else "o"
    ax.plot(solved.index, solved[solver], marker=marker, linestyle='-', label=solver)
ax.legend(title=None)
plt.xlabel("c")
plt.ylabel("Number of benchmarks solved")
plt.xticks(sorted(df["c"].unique()))
plt.tight_layout()
plt.savefig("scaling_plot.png", dpi=300, bbox_inches="tight")
plt.close()

TIMEOUT = 1800  # seconds

fig, ax = plt.subplots(figsize=(6, 4))

for solver, marker in [("cvc5", "^"), ("z3", "o")]:
    sub = df[df["solver"] == solver]

    sat = sub[sub["status"] == "sat"]
    unk = sub[sub["status"] == "unknown"]
    to = sub[sub["status"] == "timeout"]

    # SAT: filled
    ax.scatter(sat["c"], sat["time_s"], marker=marker, label=solver)

    # UNKNOWN: hollow
    ax.scatter(
        unk["c"],
        unk["time_s"],
        marker=marker,
        facecolors="none",
        edgecolors="black",
    )

    # TIMEOUT: red
    ax.scatter(
        to["c"],
        to["time_s"],
        marker=marker,
        color="red",
    )

ax.set_xlabel("c")
ax.set_ylabel("Runtime (s)")
ax.set_yscale("symlog", linthresh=0.1)
ax.set_xticks(sorted(df["c"].unique()))

handles, labels = ax.get_legend_handles_labels()
by_label = dict(zip(labels, handles))
ax.legend(by_label.values(), by_label.keys())

plt.tight_layout()
plt.savefig("scatter_runtime.png", dpi=300)
plt.close()
