"""Recompute coverage from raw LLVM exports, including Cedar-generated parsers."""
import argparse
import json
from pathlib import Path
import statistics
import sys

if __package__ in (None, ''):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.cedar.rust_replay import branch_sets, sha


def summarize(evidence):
    manifest = json.loads((evidence / 'manifest.json').read_text())
    results = json.loads((evidence / 'results.json').read_text())
    assert json.loads((evidence / 'completion.json').read_text())['status'] == 'completed'
    output = {'manifest': manifest, 'aggregation_sha256': sha(Path(__file__)),
              'adapter_sha256': sha(Path(__file__).with_name('rust_replay.py')),
              'aggregation_note': 'Recomputed from raw LLVM exports, including Cedar-generated parsers.',
              'budgets': {}}
    empty = branch_sets(json.loads((evidence / 'empty-control/coverage.json').read_text()))
    assert all(not g['covered'] for g in empty.values())
    def group_name(cohort):
        if cohort.startswith('P0-'): return 'P0'
        return cohort.rsplit('-', 1)[0] if manifest.get('mode') == 'all-versions' else cohort[:7]
    assert set(results) == {'outer-10000', 'equal-valid'}
    for budget, cohorts in results.items():
        assert set(cohorts) == set(manifest['cohorts']), 'missing or unexpected cohort'
        runs = {}
        for cohort, measured in sorted(cohorts.items()):
            run = group_name(cohort)
            scopes = branch_sets(json.loads((evidence / budget / cohort / 'coverage.json').read_text()))
            stats = runs.setdefault(run, {'inputs': 0, 'responses': {}, 'seeds': {}, 'scopes': {}})
            stats['inputs'] += measured['inputs']
            for response, count in measured['responses'].items():
                stats['responses'][response] = stats['responses'].get(response, 0) + count
            seed = cohort.rsplit('-', 1)[1]
            assert seed not in stats['seeds'], 'duplicate seed in group'
            stats['seeds'][seed] = {}
            for scope, branches in scopes.items():
                assert branches['total'] == empty[scope]['total'], 'different branch denominator'
                group = stats['scopes'].setdefault(scope, {'total': len(branches['total']),
                    'covered_union': set(), 'per_seed_covered': []})
                group['covered_union'] |= branches['covered']
                group['per_seed_covered'].append(len(branches['covered']))
                stats['seeds'][seed][scope] = len(branches['covered'])
        assert set(runs) == {group_name(k) for k in manifest['cohorts']}
        for stats in runs.values():
            assert set(stats['seeds']) == set(map(str, manifest['seeds']))
            for scope, group in stats['scopes'].items():
                baseline = runs['P0']['scopes'][scope]['covered_union']
                group['union_count'] = len(group['covered_union'])
                group['new_vs_P0'] = sorted(group['covered_union'] - baseline)
                group['missing_vs_P0'] = sorted(baseline - group['covered_union'])
                group['mean_covered'] = statistics.mean(group['per_seed_covered'])
                group['mean_percent'] = 100 * group['mean_covered'] / group['total']
        for stats in runs.values():
            for group in stats['scopes'].values():
                group['covered_union'] = sorted(group['covered_union'])
        output['budgets'][budget] = runs
    return output


def report(data):
    if data['manifest'].get('mode') == 'all-versions':
        return all_versions_report(data)
    m = data['manifest']
    lines = ['# Cedar Rust branch coverage 비교', '',
        '보존된 미사용 seed 입력을 Cedar 4.8.2의 원본 Rust 서버에 재생한 결과입니다. '
        '새 입력 생성이나 predicate 변경은 없습니다. 원본 결론과 같이 스키마와 요청 범위 아래의 정적 타입 검사를 수행하며, 정책 평가기의 실행 coverage는 아닙니다.', '',
        '## 측정 방법', '',
        '- 대상: P0, run-001/v005, run-002/v009, run-003/v004. seed: 1101, 1202, 1303, 1404, 1505.',
        '- 원 실험의 각 10,000회 생성 기록에서 확인 유효 입력만 순서와 중복을 유지하여 재생했습니다. None과 판정 불가는 Rust 입력에서 제외하지만 생성 예산에는 포함합니다.',
        f'- 보조 비교: 각 대상·seed의 처음 {m["matched_valid_inputs"]:,}개 유효 입력을 사용했습니다. 모든 군에서 같은 유효 입력 수입니다.',
        '- 빌드: rustc 1.102.0-nightly, commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973 (nightly-2026-11-21), LLVM 23.1.6. `-C instrument-coverage -Z coverage-options=branch -C debuginfo=2`.',
        '- 도구: `llvm-profdata merge`와 `llvm-cov export`. 각 군·seed·예산은 독립 프로세스와 프로파일을 사용합니다. 무입력 대조군의 Cedar branch 실행 수는 0입니다.',
        '- 분모: 같은 바이너리에서 계측된 Cedar 소스의 분기 양쪽 결과. 동일 소스 위치의 generic 인스턴스는 합칩니다. Cedar 생성 파서도 포함하며 서버·표준 라이브러리·일반 의존성은 제외합니다.',
        '- 아래 수치는 seed별 coverage의 평균입니다. 5개 seed의 합집합은 별도로 표시합니다. 작은 seed 수에 대한 기술 통계이며 유의성 검정 결과가 아닙니다.', '',
        '## 전체 생성 예산 10,000회/seed', '']
    for budget, heading in [('outer-10000', None), ('equal-valid', '## 동일 유효 입력 수 비교')]:
        if heading: lines += [heading, '']
        lines += ['| 대상 | Rust 호출 수(5 seeds) | Cedar 전체 평균 | validator 평균 | typecheck 평균 |',
                  '|---|---:|---:|---:|---:|']
        for run, stats in data['budgets'][budget].items():
            values = []
            for scope in ['cedar', 'validator', 'typecheck']:
                g = stats['scopes'][scope]
                values.append(f'{g["mean_covered"]:.1f}/{g["total"]} ({g["mean_percent"]:.2f}%)')
            lines.append(f'| {run} | {stats["inputs"]:,} | ' + ' | '.join(values) + ' |')
        lines += ['', '| 대상 | Cedar 합집합 | validator 합집합 | typecheck 합집합 |', '|---|---:|---:|---:|']
        for run, stats in data['budgets'][budget].items():
            lines.append('| ' + run + ' | ' + ' | '.join(str(stats['scopes'][s]['union_count']) for s in ['cedar','validator','typecheck']) + ' |')
        lines += ['']
    if all(runs['P0']['scopes'][scope]['mean_covered'] > runs[run]['scopes'][scope]['mean_covered']
           for runs in data['budgets'].values() for run in ['run-001', 'run-002', 'run-003']
           for scope in ['cedar', 'validator', 'typecheck']):
        lines += ['두 예산 모두에서 P0의 평균 coverage가 세 최종 후보보다 높았습니다. '
                  '이번 후보들의 유효 입력 비율 개선은 측정한 Rust 구현체의 branch coverage 개선으로 이어지지 않았습니다.', '']
    lines += ['## 판정과 해석 범위', '',
        '- 모든 Rust 응답의 원문과 개수는 summary.json과 원시 outcomes.jsonl에 있습니다. 전송/직렬화/timeout 문제는 성공으로 간주하지 않고 실행을 실패시킵니다.',
        '- `expr`만 전달하지 않습니다. 원본의 `schemaToStr`, principal/action/resource UID, `stringOfExpr`를 재현합니다. `rs`, `es`, `ty`, `PathSet`은 원본 Rust 호출 자체가 사용하지 않으며, 전체 입력 차이가 항상 서로 다른 Rust payload가 되는 것은 아닙니다.',
        f'- 대표 실제 입력 {m["oracle_samples"]}개의 변환 결과를 원본 Coq printer 정의와 구체적 등식으로 대조하고 coqchk로 검사했습니다. 별도 smoke 입력 100개에서 기존 release 서버와 계측 서버의 응답이 일치했습니다. 이는 전체 serializer에 대한 일반적 동등성 증명은 아닙니다.',
        '- 설치된 컴파일러로 별도 probe를 실행했을 때 `if`와 `if let`은 branch로 기록되고 `match`의 각 arm은 별도 branch로 기록되지 않았습니다. 이 수치는 모든 Rust 제어 흐름 간선을 포함하는 coverage 또는 MC/DC가 아닙니다.',
        '- 확인 유효 입력만 측정하므로 파싱/타입 오류 처리 분기를 모두 덮는 것이 목표가 아닙니다. 절대 비율은 대상 API에 도달하지 않는 코드도 분모에 포함하므로 상대 비교와 함께 읽어야 합니다.',
        '- 기존 탐색은 유효 비율을 피드백으로 사용했습니다. 이번 작업은 고정된 최종 후보를 사후 평가한 것으로 coverage를 최적화하는 새로운 탐색은 아닙니다.', '',
        '- 실행 중간 집계는 생성된 파서를 제외했습니다. 이 보고서와 summary.json은 원시 LLVM export에서 생성된 파서까지 포함해 다시 집계한 최종 수치입니다. 과거 로그와 실행 당시 도구 스냅샷은 그대로 보존합니다.', '',
        '## 재현', '',
        '```sh', 'bash environment/env.sh setup-cedar-coverage',
        'python3 -B scripts/cedar/rust_replay.py \\',
        '  --source properties/cedar_no_type_error/.runs/cedar-remeasure-20261122T131403Z \\',
        '  --output properties/cedar_no_type_error/.runs/cedar-rust-coverage-NEW',
        'python3 -B scripts/cedar/report_rust_coverage.py \\',
        '  --evidence properties/cedar_no_type_error/.runs/cedar-rust-coverage-NEW \\',
        '  --output properties/cedar_no_type_error/experiments/cedar-rust-coverage-NEW', '```', '',
        'Rust 계측: [공식 compiler coverage 옵션](https://doc.rust-lang.org/stable/unstable-book/compiler-flags/coverage-options.html), '
        '[LLVM 도구 사용](https://doc.rust-lang.org/rustc/instrument-coverage.html).', '']
    return '\n'.join(lines)


def all_versions_report(data):
    m = data['manifest']
    k = m['matched_valid_inputs']
    lines = ['# Cedar Rust branch coverage: 전체 채택 버전', '',
        'P0와 run-001의 v001–v005, run-002의 v001–v009, run-003의 v001–v004를 비교했습니다. '
        '평가 seed 101/202/303/404/505의 저장 입력을 사용했습니다. 중간 버전에는 저장된 미사용 seed 입력이 없으므로 '
        '기존 최종 버전의 미사용 seed 결과와 별도 실험입니다. 입력 재생성과 predicate 변경은 없습니다.', '',
        '## 측정 조건', '',
        '- 대상은 Cedar 4.8.2 원본 Rust 서버의 strict 정적 타입 검사입니다. 식뿐 아니라 스키마와 요청 범위도 전달합니다. 정책 평가기 coverage는 아닙니다.',
        '- rustc nightly-2026-11-21 (c7d5ba59d8e11ee2e2204b173458eec4cb41c973), LLVM 23.1.6. '
        '`-C instrument-coverage -Z coverage-options=branch -C debuginfo=2`; `llvm-profdata merge` 및 `llvm-cov export`를 사용했습니다.',
        '- 같은 계측 바이너리, 생성 파서를 포함한 Cedar 소스 분모를 사용했습니다. generic 인스턴스의 동일 소스 분기 결과는 합칩니다. 서버와 일반 의존성은 제외합니다.',
        '- 각 대상·seed의 10,000회 생성 시도에서 확인 유효 입력을 순서와 중복을 유지하여 모두 재생합니다. None과 판정 불가는 생성 예산에 포함하지만 Rust에는 보내지 않습니다.',
        f'- 동일 입력 예산은 모든 대상·seed에서 처음 {k:,}개 유효 입력입니다. 전체 95개 군의 최소 유효 입력 수로 맞췄습니다. '
        '생성률이 낮은 중간 버전 때문에 기존 최종 버전 비교의 7,829개보다 작습니다. 두 실험의 수치를 직접 연결하면 안 됩니다.',
        '- 표의 coverage는 seed별 비율의 산술평균입니다. 합집합은 별도 표에 있습니다. 버전끼리는 독립 표본이 아니며 유의성이나 단조 관계를 주장하지 않습니다.', '',
        '## 전체 생성 예산: 10,000회/seed', '',
        '| 대상 | 확인 유효 비율 | Rust 호출(5 seeds) | Cedar 평균 | validator 평균 | typecheck 평균 |',
        '|---|---:|---:|---:|---:|---:|']
    outer = data['budgets']['outer-10000']
    for group, stats in outer.items():
        values = [f'{stats["scopes"][s]["mean_covered"]:.1f}/{stats["scopes"][s]["total"]} '
                  f'({stats["scopes"][s]["mean_percent"]:.2f}%)' for s in ['cedar', 'validator', 'typecheck']]
        lines.append(f'| {group} | {100 * stats["inputs"] / 50000:.3f}% | {stats["inputs"]:,} | ' + ' | '.join(values) + ' |')
    lines += ['', f'## 동일 유효 입력 예산: {k:,}개/seed', '',
        '| 대상 | Rust 호출(5 seeds) | Cedar 평균 | validator 평균 | typecheck 평균 |',
        '|---|---:|---:|---:|---:|']
    for group, stats in data['budgets']['equal-valid'].items():
        values = [f'{stats["scopes"][s]["mean_covered"]:.1f}/{stats["scopes"][s]["total"]} '
                  f'({stats["scopes"][s]["mean_percent"]:.2f}%)' for s in ['cedar', 'validator', 'typecheck']]
        lines.append(f'| {group} | {stats["inputs"]:,} | ' + ' | '.join(values) + ' |')
    lines += ['', '## Cedar 분기 결과 합집합', '',
        '새 분기와 누락 분기는 같은 예산의 P0 합집합을 기준으로 셉니다. 합집합은 seed별 평균과 다릅니다.', '',
        '| 대상 | 전체 예산 합집합 | 새 분기 / 누락 | 동일 입력 합집합 | 새 분기 / 누락 |',
        '|---|---:|---:|---:|---:|']
    for name in outer:
        cells = []
        for budget in ['outer-10000', 'equal-valid']:
            g = data['budgets'][budget][name]['scopes']['cedar']
            cells += [str(g['union_count']), f'{len(g["new_vs_P0"])} / {len(g["missing_vs_P0"])}']
        lines.append('| ' + name + ' | ' + ' | '.join(cells) + ' |')
    calls = sum(s['inputs'] for runs in data['budgets'].values() for s in runs.values())
    responses = {}
    for runs in data['budgets'].values():
        for s in runs.values():
            for response, count in s['responses'].items():
                responses[response] = responses.get(response, 0) + count
    lines += ['', '## 검증과 해석 범위', '',
        f'- Rust 호출 총 {calls:,}회, 응답별 개수: `{json.dumps(responses, sort_keys=True)}`. 두 예산의 입력은 겹칩니다.',
        f'- 대표 실제 입력 {m["oracle_samples"]:,}개를 upstream Coq serializer와 구체적 등식으로 대조하고 커널 검사했습니다. 전체 직렬화 동등성 정리는 아닙니다.',
        '- 무입력 대조군에서 Cedar 분기 실행은 0입니다. 모든 군의 분모 동일성과 종료 시 바이너리 해시를 검사합니다.',
        '- 이 컴파일러의 branch 계측은 `if`/`if let`을 기록하지만 `match`의 각 arm을 별도로 기록하지 않습니다. 전체 제어 흐름이나 MC/DC가 아닙니다.',
        '- coverage는 이 API와 표본에서 실행한 계측 분기의 폭입니다. 입력 공간 전체의 다양성과 동일한 개념이 아닙니다. 절대 비율의 분모에는 해당 API에서 도달하지 않는 코드도 있습니다.',
        '- 기존 탐색의 피드백은 유효 비율이었습니다. 이 결과는 채택 버전의 사후 평가이며 coverage 최적화 탐색이 아닙니다.', '',
        '## 재현', '', '```sh',
        'python3 -B scripts/cedar/rust_replay.py --mode all-versions \\',
        '  --source properties/cedar_no_type_error/.runs/cedar-remeasure-20261122T131403Z \\',
        '  --output properties/cedar_no_type_error/.runs/cedar-rust-coverage-all-NEW --workers 8',
        'python3 -B scripts/cedar/report_rust_coverage.py \\',
        '  --evidence properties/cedar_no_type_error/.runs/cedar-rust-coverage-all-NEW \\',
        '  --output properties/cedar_no_type_error/experiments/cedar-rust-coverage-all-NEW',
        'python3 -B scripts/cedar/plot_rust_coverage.py \\',
        '  --summary properties/cedar_no_type_error/experiments/cedar-rust-coverage-all-NEW/summary.json \\',
        '  --output properties/cedar_no_type_error/experiments/cedar-rust-coverage-all-NEW/figures',
        '```', '', '그림 생성에는 Matplotlib이 필요합니다.', '']
    return '\n'.join(lines)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    data = summarize(args.evidence)
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'summary.json').write_text(json.dumps(data, indent=2))
    (args.output / 'RESULTS.md').write_text(report(data))
