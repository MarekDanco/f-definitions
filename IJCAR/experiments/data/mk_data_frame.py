from pathlib import Path
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

C_MAP = {
    "bench10_2000_40000": 1,
    "bench100_2000_40000": 2,
    "bench1000_2000_40000": 3,
    "bench10000_2000_40000": 4,
    "bench100000_2000_40000": 5,
    "bench_2000_40000": "✱",
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
pd.set_option('display.max_rows', None)
print(df[df["c"] == "✱"])
c_to_numeric = {1: 1, 2: 2, 3: 3, 4: 4, 5: 5, "✱": 6}
df["c_numeric"] = df["c"].map(c_to_numeric)

solved = df[df["status"] == "sat"].groupby(["c", "solver"]).size().unstack(fill_value=0)

# Create numeric index for plotting
solved_numeric = (
    df[df["status"] == "sat"]
    .assign(c_numeric=df["c_numeric"])
    .groupby(["c_numeric", "solver"])
    .size()
    .unstack(fill_value=0)
)

fig, ax = plt.subplots()
for solver in solved_numeric.columns:
    marker = "^" if solver == "cvc5" else "o"
    ax.plot(
        solved_numeric.index,
        solved_numeric[solver],
        marker=marker,
        linestyle="-",
        label=solver,
    )
ax.legend(title=None)
plt.xlabel("c")
plt.ylabel("Number of problems solved")

# Set custom tick labels
tick_positions = sorted(c_to_numeric.values())
tick_labels = [k for k, v in sorted(c_to_numeric.items(), key=lambda x: x[1])]
plt.xticks(tick_positions, tick_labels)

plt.tight_layout()
plt.savefig("scaling_plot.png", dpi=300, bbox_inches="tight")
plt.close()

TIMEOUT = 1800
fig, axes = plt.subplots(1, 2, figsize=(9, 3), sharey=True)
cs = sorted(df[df["c"].isin([2, 3])]["c"].unique())
for ax, c in zip(axes, cs):
    sub = df[(df["c"] == c) & (df["solver"] == "cvc5")]
    solved = sub[sub["status"] == "sat"]["time_s"]
    times = np.sort(solved.values)
    x = np.arange(1, len(times) + 1)
    ax.plot(
        x,
        times,
        marker="^",
        markersize=4,
        linewidth=1.5,
    )
    ax.set_title(f"c = {c}")
    ax.set_xlabel("Number of problems solved")
    ax.set_yscale("symlog", linthresh=0.1)
    ax.set_ylim(0, TIMEOUT)
axes[0].set_ylabel("Runtime (s)")
plt.tight_layout()
plt.savefig("cactus_plot.png", dpi=300)
plt.close()
