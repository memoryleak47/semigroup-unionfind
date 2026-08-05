#!/usr/bin/python3 -B

import os
import sys
import matplotlib.pyplot as plt
import numpy as np

def read(x):
    try:
        with open(x, "r") as file:
            content = file.read()
        return content
    except FileNotFoundError:
        return None

def parse_num(s):
    try:
        return int(s)
    except ValueError:
        return float(s)

# returns list of entries, or None
def get_entry_file(act):
    filename = f"benchdata/entries-{act}.txt"
    data = read(filename)
    if data is None: return None

    out = []

    entries = []
    for line in data.splitlines():
        if line.startswith("#START"):
            out.append(entries)
            entries = []
        else:
            entries.append(parse_entry(line))

    if len(entries) > 0:
        out.append(entries)

    return out

def parse_entry(entry):
    total_size = parse_num(entry.split("total_size=")[1].split(",")[0])
    time = parse_num(entry.split("time=")[1].split(",")[0])
    iteration = parse_num(entry.split("iteration=")[1].split(",")[0])
    stop = entry.split("stop=")[1].strip()

    return {
        "costs": [],
        "total_size": total_size,
        "time": time,
        "iteration": iteration,
        "stop": stop,
    }

db = {}
for act in ["active", "passive"]:
    db[act] = get_entry_file(act)

assert(len(db["active"]) == len(db["passive"]))

def solve_time(entries):
    for e in entries:
        if "PROOF FOUND" in e["stop"]:
            return e["time"]

def get_solveds(act):
    out = []
    for entries in db[act]:
        s = solve_time(entries)
        if s:
            out.append(s)
    return sorted(out)

out_active = get_solveds("active")
out_passive = get_solveds("passive")

active_sorted = sorted(out_active)
passive_sorted = sorted(out_passive)

plt.figure(figsize=(8, 5))

# Plot active (blue) and passive (red)
plt.plot(range(1, len(active_sorted) + 1), active_sorted, color='blue', marker='o', drawstyle='steps-post', label='Active')
plt.plot(range(1, len(passive_sorted) + 1), passive_sorted, color='red', marker='o', drawstyle='steps-post', label='Passive')

plt.xlabel('Number of Solved Instances')
plt.ylabel('Time (seconds)')
plt.title('Cactus Plot Comparison')
plt.yscale('log')
plt.grid(True, which='both', linestyle='--', alpha=0.5)
plt.legend()
plt.tight_layout()

plt.show()
