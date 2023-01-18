import matplotlib.pyplot as plt
import numpy as np

def cactas(values, label, line_info, mn, mx, filename, div = 10000):
    y = np.arange(mn, mx, (mx-mn) / div)
    x = [0] * div
    w = (mx - mn) / div

    idx = 0
    for v in values:
        n = int((v - mn)/w)
        x[n] += 1
        idx = max(idx, n)

    tmp = list(filter(lambda x: x[0] > 0, zip(x, y)))
    x = list(map(lambda x: x[0], tmp))
    y = list(map(lambda x: x[1], tmp))
    for i in range(len(x) - 1):
        x[i+1] += x[i]
    plt.plot(x[:idx], y[:idx], label=label, linewidth=line_info[0], linestyle=line_info[1], color=line_info[2])
    print(x[-1])
    ax = plt.gca()
    ax.spines['top'].set_color('none')

    x_label = 'Benchmarks passed (of 127)'
    y_label = 'Time in seconds'
    plt.xlabel(x_label, fontsize=18)
    plt.ylabel(y_label, fontsize=18)
    plt.legend()
    if False:
        plt.title(filename)
    plt.grid(which="both")

def plot_graph(filename, label, line_info):
    solved = None
    with open (filename) as f:
        s = list(map(lambda line: line.split(','), f.readlines()))
        solved = sorted(list(map(lambda x: float(x[2]), filter(lambda l: l[1] == "sat" or l[1] == "unsat", s))))
    cactas(solved, label, line_info, 0, 300, filename)

def line_width_of_domain(domain):
    if domain == "interval":
        return 2
    elif domain == "octagon":
        return 2
    elif domain == "octahedron":
        return 2
    else:
        return 2

def line_style_of_domain(domain):
    if domain == "interval":
        return "dashdot"
    elif domain == "octagon":
        return "--"
    elif domain == "octahedron":
        return ":"
    else:
        return "-"

def line_color_of_domain(domain):
    if domain == "interval":
        return "g"
    elif domain == "octagon":
        return "r"
    elif domain == "octahedron":
        return "c"
    else:
        return "m"    

def line_info_of_domain(domain):
    return (
        line_width_of_domain(domain),
        line_style_of_domain(domain),
        line_color_of_domain(domain)
    )

if __name__ == "__main__":
    BIG_NUM_FOR_INDEX = 100000
    files = [
        # (sort_key, filename, label, line_info = (line_width, line_style, line_color))
        (-1, 'result/sygus18inv/ucore.csv', 'Stratified', (2, "-", "b")),
        (BIG_NUM_FOR_INDEX + 1, 'result/sygus18inv/loopinvgen.csv', 'LoopInvGen', (2, "dashdot", "y")),
        (BIG_NUM_FOR_INDEX + 2, 'result/sygus18inv/hoice.csv', 'Hoice', (2, "--", "orangered")),
        (BIG_NUM_FOR_INDEX + 3, 'result/sygus18inv/spacer.csv', 'Spacer', (2, ":", "k"))
    ]

    for idx_of_domain, domain in enumerate(["interval", "octagon", "octahedron", "polyhedron"]):
        filename = 'result/sygus18inv/tb_{}_domain_4_null.csv'.format(domain)
        label = domain.upper()
        files.append((idx_of_domain, filename, label, line_info_of_domain(domain)))

    # sorted by sort_key
    files.sort()

    for _, f, label, line_info in files:
        print(f)
        plot_graph(f, label, line_info)

    plt.show()
