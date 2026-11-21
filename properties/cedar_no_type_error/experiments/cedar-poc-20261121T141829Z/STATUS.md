# 중단된 Cedar 실험 기록

실험 ID: `cedar-poc-20261121T141829Z`

상태: **중단 / 최종 평가 미완료**. Coq가 forall 뒤에 출력한 줄바꿈을 형태 검사기가 잘못 처리하여 정상적인 두 번째 제안을 거절했습니다. 이 일반적인 검사기 오류를 수정하기 위해 세 번째 Reformulator 호출을 중단했습니다. 이 실험은 완료된 3-run 실험이 아니며, 다음 실험은 새 ID에서 baseline부터 다시 실행합니다.

원시 역할 이벤트, 미완료 배치, 모든 샘플·판정·검사 로그는 다음 ignored 경로에 보존되어 있습니다.

`properties/cedar_no_type_error/.runs/cedar-poc-20261121T141829Z/`

`manifest.json`은 해당 실행의 고정 commit·소스·도구·조건 해시를, `summary.json`은 실제 완료 집계와 모든 제안의 역할별 비용을 보존합니다. `coordinator-stop.json`은 의도적인 중단 사유를 기록합니다.

| run | 제안 수 | 채택 수 | 상태 |
|---|---:|---:|---|
| run-001 | 3 | 1 | operational_failure: reformulator |
| run-002 | 0 | 0 | not_run_due_to_operational_failure |
| run-003 | 0 | 0 | not_run_due_to_operational_failure |

완료된 평가 baseline: 193/50000 = 0.386%, 판정 불가 3259회.
run-001/v001: 41/50000 = 0.082%, 판정 불가 382회. 해당 후보의 동등성·생성·측정은 완료됐지만 실험 전체는 중단됐습니다.

미사용 seed 재평가는 실행하지 않았습니다. 위 관측값은 다음 실험의 baseline·후보 피드백·집계에 합치지 않습니다. 샘플링과 커널 검사는 생성기 soundness/completeness 증명이 아닙니다.
