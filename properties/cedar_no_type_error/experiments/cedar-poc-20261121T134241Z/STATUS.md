# 중단된 Cedar 실험 기록

실험 ID: `cedar-poc-20261121T134241Z`

상태: **중단 / 최종 평가 미완료**. 직렬 판정 실행을 중단하고 동결된 병렬 실행 도구로 교체했습니다. baseline은 완료되지 않았고 역할 호출도 시작되지 않았습니다. 부분 측정은 후속 실험에 재사용하지 않았습니다.

원시 역할 이벤트, 미완료 배치, 모든 샘플·판정·검사 로그는 다음 ignored 경로에 보존되어 있습니다.

`properties/cedar_no_type_error/.runs/cedar-poc-20261121T134241Z/`

`manifest.json`은 해당 실행의 고정 commit·소스·도구·조건 해시를, `summary.json`은 실제 완료 집계와 모든 제안의 역할별 비용을 보존합니다. `coordinator-stop.json`은 의도적인 중단 사유를 기록합니다.

| run | 제안 수 | 채택 수 | 상태 |
|---|---:|---:|---|
| run-001 | 0 | 0 | not_run_due_to_operational_failure |
| run-002 | 0 | 0 | not_run_due_to_operational_failure |
| run-003 | 0 | 0 | not_run_due_to_operational_failure |

미사용 seed 재평가는 실행하지 않았습니다. 위 관측값은 다음 실험의 baseline·후보 피드백·집계에 합치지 않습니다. 샘플링과 커널 검사는 생성기 soundness/completeness 증명이 아닙니다.
