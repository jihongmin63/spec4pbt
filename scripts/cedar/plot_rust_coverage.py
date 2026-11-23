"""Fig. 1: generation yield and measured Rust branch coverage for every version.

Requires Matplotlib. Values are read only from the audited coverage summary;
CSV and provenance accompany the PNG, SVG and PDF exports.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

# Categorical slots 1-3 of the validated reference palette (all-pairs CVD
# Delta E 9.2, normal-vision 24.0). Text uses a darker step of the same hue
# (>= 4.5:1 on white); shapes repeat the run identity for grayscale readers.
STYLE = {
    'run-001': {'fill': '#2a78d6', 'ink': '#1c5cab', 'marker': 'o'},
    'run-002': {'fill': '#eb6834', 'ink': '#b5461b', 'marker': 's'},
    'run-003': {'fill': '#1baf7a', 'ink': '#0d7a55', 'marker': '^'},
}
INK, INK2, MUTED, GRID = '#0b0b0b', '#52514e', '#898781', '#e1e0d9'
# Label offsets (points) for the only labelled marks: each run's final version.
FINAL_LABEL = {'run-001': (10, 6, 'left', 'bottom'), 'run-002': (-12, 0, 'right', 'center'),
               'run-003': (-10, -8, 'right', 'top')}
# Two runs leave P0 for the same low-validity measurement; opposite slight
# bows keep their arrows apart. All other steps are straight.
CURVE = {('run-002', 'v002'): .06, ('run-003', 'v001'): -.06}
TRACK = 3.2  # points between parallel arrows of runs that took the identical step


def plot(summary, output):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    from matplotlib.patches import FancyArrowPatch
    from matplotlib.transforms import ScaledTranslation
    from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator
    data = json.loads(summary.read_text())
    m = data['manifest']
    assert m['mode'] == 'all-versions'
    output.mkdir(parents=True, exist_ok=True)
    outer, equal = [data['budgets'][b] for b in ['outer-10000', 'equal-valid']]
    runs = sorted({name.rsplit('-', 1)[0] for name in outer if name != 'P0'})
    assert runs == sorted(STYLE)
    chains = {run: ['P0'] + sorted(n for n in outer if n.startswith(run + '-')) for run in runs}
    x, y, rows = {}, {}, []
    for run in runs:
        for name in chains[run]:
            prefix = 'P0-P0-' if name == 'P0' else name + '-'
            cohorts = [v['counts'] for key, v in m['cohorts'].items() if key.startswith(prefix)]
            assert len(cohorts) == len(m['seeds'])
            value = sum(100 * c['valid'] / c['attempts'] for c in cohorts) / len(cohorts)
            x[name], y[name] = value / 100, outer[name]['scopes']['cedar']['mean_percent']
            rows.append({'run': run, 'version': 'P0' if name == 'P0' else name.rsplit('-', 1)[1],
                         'valid_percent': value, 'outer_cedar_percent': y[name],
                         'equal_cedar_percent': equal[name]['scopes']['cedar']['mean_percent']})
    finals = {run: chains[run][-1] for run in runs}
    assert all(y[name] < y['P0'] for name in y if name != 'P0')  # the subtitle's claim

    plt.rcParams.update({
        'font.size': 11, 'axes.spines.top': False, 'axes.spines.right': False,
        'axes.edgecolor': '#c3c2b7', 'axes.labelcolor': INK2, 'xtick.color': INK2,
        'ytick.color': INK2, 'xtick.major.size': 0, 'ytick.major.size': 0,
        'svg.fonttype': 'none', 'svg.hashsalt': 'fig1-rust-coverage', 'pdf.fonttype': 42})
    fig, ax = plt.subplots(figsize=(10.5, 6.6))
    fig.subplots_adjust(left=.085, right=.97, top=.9, bottom=.22)

    ax.set_xscale('logit')
    ax.set_xlim(.07, .999996)
    ax.xaxis.set_major_locator(FixedLocator([.1, .5, .9, .99, .999, .9999, .99999]))
    ax.xaxis.set_major_formatter(FuncFormatter(
        lambda v, _: f'{100 * v:.{max(0, round(-math.log10(1 - v)) - 2)}f}%'))
    ax.xaxis.set_minor_locator(NullLocator())
    ax.set_ylim(min(y.values()) - .25, max(y.values()) + .25)
    ax.yaxis.set_major_locator(FixedLocator([v / 2 for v in range(0, 40)]))
    ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f'{v:g}%'))
    ax.grid(color=GRID, lw=.8)
    ax.set_axisbelow(True)
    ax.set_xlabel('Valid inputs / generation attempts (logit scale)', labelpad=8)
    ax.set_ylabel('Cedar branch coverage', labelpad=8)

    ax.axhline(y['P0'], color=MUTED, lw=1, ls=(0, (3, 3)), zorder=1)
    ax.text(.9999955, y['P0'] + .03, f'P0 level  {y["P0"]:.2f}%', ha='right', va='bottom',
            fontsize=10, color=INK2)

    # Adoption steps, one arrow per run. Runs that took the identical step get
    # parallel arrows side by side instead of one hidden under the other.
    edges = {}
    for run in runs:
        for before, after in zip(chains[run], chains[run][1:]):
            edges.setdefault(((x[before], y[before]), (x[after], y[after])), []).append((run, after))
    for (start, end), owners in edges.items():
        (sx, sy), (ex, ey) = ax.transData.transform([start, end])
        length = math.hypot(ex - sx, ey - sy)
        nx, ny = -(ey - sy) / length, (ex - sx) / length
        for k, (run, after) in enumerate(owners):
            shift = (k - (len(owners) - 1) / 2) * TRACK / 72
            rad = CURVE.get((run, after.rsplit('-', 1)[1]), 0)
            ax.add_patch(FancyArrowPatch(
                start, end, arrowstyle='-|>', mutation_scale=11, shrinkA=5, shrinkB=6,
                connectionstyle=f'arc3,rad={rad}', color=STYLE[run]['fill'], lw=1.7, alpha=.9, zorder=3,
                transform=ax.transData + ScaledTranslation(nx * shift, ny * shift, fig.dpi_scale_trans)))

    # Versions; a measurement two runs share is one two-color point.
    groups = {}
    for run in runs:
        for name in chains[run][1:]:
            groups.setdefault((x[name], y[name]), []).append(run)
    for (px, py), owners in groups.items():
        if len(owners) == 2:
            ax.plot(px, py, marker='o', markersize=8, fillstyle='left', ls='',
                    markerfacecolor=STYLE[owners[0]]['fill'], markerfacecoloralt=STYLE[owners[1]]['fill'],
                    markeredgecolor='white', markeredgewidth=1.1, zorder=5)
            continue
        run, = owners
        ax.scatter(px, py, s=38, marker=STYLE[run]['marker'], c=STYLE[run]['fill'],
                   edgecolors='white', linewidths=1, zorder=5)
    for run, name in finals.items():
        ax.scatter(x[name], y[name], s=120, marker=STYLE[run]['marker'], c=STYLE[run]['fill'],
                   edgecolors=INK, linewidths=1.5, zorder=6)
        dx, dy, ha, va = FINAL_LABEL[run]
        ax.annotate(f'{y[name]:.2f}%', (x[name], y[name]), xytext=(dx, dy), textcoords='offset points',
                    ha=ha, va=va, fontsize=11, weight='bold', color=STYLE[run]['ink'], zorder=7,
                    bbox={'facecolor': 'white', 'edgecolor': 'none', 'alpha': .85, 'pad': .5})
    ax.scatter(x['P0'], y['P0'], s=110, marker='D', c=INK, edgecolors='white', linewidths=1.2, zorder=6)
    ax.annotate('P0', (x['P0'], y['P0']), xytext=(0, 9), textcoords='offset points',
                ha='center', va='bottom', fontsize=11, weight='bold', color=INK, zorder=7)

    handles = [Line2D([0], [0], color=STYLE[r]['fill'], marker=STYLE[r]['marker'], markersize=7,
                      markeredgecolor='white', lw=1.7, label=r) for r in runs] + [
        Line2D([0], [0], ls='', marker='o', markersize=9, markerfacecolor='#dcdbd6',
               markeredgecolor=INK, markeredgewidth=1.5, label='final version')]
    fig.legend(handles=handles, loc='upper left', bbox_to_anchor=(.024, .985), ncols=4,
               frameon=False, fontsize=10.5, handlelength=2.2, columnspacing=1.8, labelcolor=INK)
    # Caption below the figure.
    fig.text(.03, .095, 'Fig. 1  Valid-input ratio and Rust branch coverage across adopted reformulations',
             fontsize=13, weight='bold', color=INK, va='top')
    fig.text(.03, .055, 'Mean of 5 seeds; all valid inputs from 10,000 generation attempts per seed, '
             'run on Cedar 4.8.2 strict type validation.\nTwo-color points and paired arrows: '
             'two runs reached the same reformulation.', fontsize=9.5, color=INK2, va='top', linespacing=1.4)

    for extension, meta in [('png', {}), ('svg', {'Date': None}), ('pdf', {'CreationDate': None})]:
        fig.savefig(output / ('fig1-rust-coverage.' + extension), dpi=200, facecolor='white', metadata=meta)
    plt.close(fig)
    with (output / 'fig1-data.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)
    (output / 'fig1-provenance.json').write_text(json.dumps({
        'summary_sha256': hashlib.sha256(summary.read_bytes()).hexdigest(),
        'plot_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'matplotlib': matplotlib.__version__, 'seeds': m['seeds'],
        'matched_valid_inputs': m['matched_valid_inputs'], 'scope': 'cedar',
        'aggregation': 'mean across seeds',
        'layout': 'single panel; all runs overlaid; x=valid fraction, y=Cedar branch coverage (%); '
                  'only P0 and final versions labelled',
        'displayed_budget': 'outer-10000', 'x_scale': 'logit',
        'uncertainty': 'omitted in overview; per-seed values in summary.json',
        'palette': {run: s['fill'] for run, s in STYLE.items()},
        'outputs_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sorted(output.glob('fig1-*')) if p.suffix != '.json'}}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--summary', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    plot(args.summary, args.output)
