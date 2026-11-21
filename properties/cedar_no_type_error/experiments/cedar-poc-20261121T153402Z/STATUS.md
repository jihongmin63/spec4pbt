# 중단된 Cedar 실험 기록

실험 ID: `cedar-poc-20261121T153402Z`. 상태: **중단 / 최종 평가 미완료**.

Coq가 선행 후보의 검증된 귀납 helper 이름을 Candidate.SeedSchema로 줄여 출력했는데, 형태 검사기가 긴 이름만 허용하여 두 번째 제안을 잘못 거절했습니다. 일반적인 관계 이름 해석을 수정하기 위해 세 번째 Reformulator 호출을 중단했습니다. 이 기록은 완료된 3-run 실험이 아닙니다.

고정 commit·소스·도구·실행 조건은 [manifest.json](manifest.json), 모든 실제 seed 집계와 제안별 역할 비용은 [summary.json](summary.json), 의도적 중단 사유는 [coordinator-stop.json](coordinator-stop.json)에 보존합니다.

| run | 제안 수 | 채택 수 | 상태 |
|---|---:|---:|---|
| run-001 | 3 | 1 | operational_failure: reformulator |
| run-002 | 0 | 0 | not_run_due_to_operational_failure |
| run-003 | 0 | 0 | not_run_due_to_operational_failure |

완료된 평가 baseline: 193/50,000 = 0.386%, 판정 불가 3,259회.
run-001/v001: 50,000/50,000 = 100%, 판정 불가 0회. P0 대비 +99.614%p. 이 후보는 별도 동등성 증명, 전체 prefix, 독립 검사, 자동 도출 및 입력 판정을 완료했습니다.

v001은 간단한 타입 표현식 7개와 일반 경우를 귀납 constructor로 표현합니다. 위 수치는 고정 size=2와 평가 seed에서의 관측이며 생성기 정확성·완전성의 증명이 아닙니다.

미사용 seed 재평가는 실행하지 않았습니다. 다음 실험은 새 ID에서 baseline부터 실행하며, 이전 측정·후보·피드백을 재사용하지 않습니다.

모든 원시 이벤트·usage·실패 제안·샘플·Coq 증거는 `properties/cedar_no_type_error/.runs/cedar-poc-20261121T153402Z/`에 보존했습니다. 중단된 역할의 누락 usage는 unavailable이며 호출하지 않은 Prover는 not_run입니다.
