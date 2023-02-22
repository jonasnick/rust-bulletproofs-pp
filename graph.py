import math
import matplotlib.pyplot as plt
import numpy as np

import csv

prover_data = []
verifier_data = []
with open('data.txt', newline='') as csvfile:
    spamreader = csv.reader(csvfile, delimiter=',', quotechar='|')
    prover_line = True
    for row in spamreader:
        if prover_line:
            prover_data.append((float(row[1]), float(row[2]), float(row[3])))
        else:
            verifier_data.append((float(row[1]), float(row[2]), float(row[3])))
        prover_line = not prover_line

p_avgs = [x[1]/1000 for x in prover_data]
v_avgs = [x[1]/1000 for x in verifier_data]
xticks = [2**(x + 1) for x in range(len(p_avgs))]
xpoints = [x + 1 for x in range(len(p_avgs))]
yticks = [10**x for x in range(-1, 4)]

prover_bench = np.array(p_avgs)
verifier_bench = np.array(v_avgs)

plt.xticks(xpoints, xticks)
plt.yscale('log')
plt.xlabel('Number of rangeproof bits')
plt.ylabel('T (ms)')
plt.ylim(0.1, 1000)
plt.plot(xpoints, prover_bench, linestyle = 'dotted', marker = 'o', color = 'r', label = "Prover Time(ms)")
plt.plot(xpoints, verifier_bench, linestyle = 'dotted', marker = 5, color = 'b', label = "Verifier Time(ms)")
plt.legend()
plt.show()



