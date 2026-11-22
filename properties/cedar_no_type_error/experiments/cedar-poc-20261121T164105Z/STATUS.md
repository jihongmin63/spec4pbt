# 중단 실행 기록

실험 `cedar-poc-20261121T164105Z`은 **중단**됐습니다. 고정 commit은 `205fe5d66a1534aabcfe476f3258dc6d3d29ddb3`입니다. 새 실험의 결과로 합산하거나 재사용하지 않습니다.

첫 두 run은 각각 10회 제안 한도를 완료했습니다. run-003의 세 번째 제안에서 Coq `About` 출력 줄바꿈 때문에 유효한 귀납 관계가 형태 검사에서 잘못 거절된 것을 확인했습니다. 실제 출력은 `Expands to: Inductive` 다음 줄에 정규화된 전체 관계 이름을 표시했지만, 동결된 검사기의 정규식은 한 줄을 요구했습니다. 이 검사기 제한은 해당 제안과 이후 탐색에 영향을 주므로 완결된 실험으로 보고하지 않습니다.

조정자를 SIGINT로 종료했습니다. run-003 attempt-004는 Reformulator와 Prover가 완료된 뒤 전체 prefix 검사 중 중단됐으며 채택하지 않았습니다. 두 역할의 실제 시간·usage는 보존됐습니다. 최종 미사용 seed 평가는 실행하지 않았습니다. 도구 수정과 새 독립 검토 후 별도 ID에서 P0부터 다시 실행해야 합니다.

조건: size=2, 평가 seed 101/202/303/404/505, seed당 외부 생성 호출 10,000회. 확인 유효 비율은 원본 다섯 전제를 모두 확인한 입력 수 / 전체 외부 호출 수입니다. 판정 불가는 유효·무효로 추정하지 않습니다. 생성기 정확성·완전성의 증명이 아닙니다.

## 실행별 종료 상태

| run | 제안 | 채택 | 마지막 | 최고 | 종료 |
|---|---:|---:|---|---|---|
| run-001 | 10 | 8 | v008 | v001 | attempt_limit |
| run-002 | 10 | 7 | v007 | v007 | attempt_limit |
| run-003 | 4 | 1 | v001 | v001 | operational_failure |

## 제안별 결과

| run / 제안 | 판정 | 채택 | 확인 유효 비율 | P0 대비 %p | 직전 대비 %p | 판정 불가 | 사유 |
|---|---|---|---:|---:|---:|---:|---|
| run-001/attempt-001 | adopted | v001 | 100.000% | +99.614 | +99.614 | 0 | verified |
| run-001/attempt-002 | adopted | v002 | 94.762% | +94.376 | -5.238 | 2619 | verified |
| run-001/attempt-003 | adopted | v003 | 77.222% | +76.836 | -17.540 | 11389 | verified |
| run-001/attempt-004 | adopted | v004 | 57.604% | +57.218 | -19.618 | 21198 | verified |
| run-001/attempt-005 | adopted | v005 | 29.220% | +28.834 | -28.384 | 35390 | verified |
| run-001/attempt-006 | adopted | v006 | 47.962% | +47.576 | +18.742 | 26019 | verified |
| run-001/attempt-007 | adopted | v007 | 36.606% | +36.220 | -11.356 | 31697 | verified |
| run-001/attempt-008 | adopted | v008 | 21.854% | +21.468 | -14.752 | 39073 | verified |
| run-001/attempt-009 | rejected | — | — | — | — | — | prover 제출=rejected; 응답=proved; 변경 파일=['.Equivalence.aux', 'Equivalence.v']; violations=[]; 원시 사유/자기 보고=Equivalence.v proves the exact supplied theorem. Coq compilation and coqchk pass; the proof has no additional assumptions. |
| run-001/attempt-010 | rejected | — | — | — | — | — | prover 제출=rejected; 응답=missing; 변경 파일=['Equivalence.v']; violations=[]; 원시 사유/자기 보고=proof failed |
| run-002/attempt-001 | rejected | — | — | — | — | — | inspector 제출=rejected; 응답=passed; 변경 파일=['scripts/__pycache__/check.cpython-314.pyc', 'scripts/cedar/__pycache__/__init__.cpython-314.pyc', 'scripts/cedar/__pycache__/serialization.cpython-314.pyc']; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261121T164105Z/run-002/attempt-001/roles/inspector-dddcd7d951804634b9f22d2bdd68e05d/private-evidence/result.json |
| run-002/attempt-002 | adopted | v001 | 0.306% | -0.080 | -0.080 | 2991 | verified |
| run-002/attempt-003 | adopted | v002 | 5.862% | +5.476 | +5.556 | 4144 | verified |
| run-002/attempt-004 | adopted | v003 | 3.628% | +3.242 | -2.234 | 1452 | verified |
| run-002/attempt-005 | adopted | v004 | 1.474% | +1.088 | -2.154 | 836 | verified |
| run-002/attempt-006 | rejected | — | — | — | — | — | inspector 제출=accepted; 응답=failed; 변경 파일=[]; violations=['v005 fails the required Testing Theorems derivation at `quickchick 2.`: Coq reports that `left` is applied to no arguments. No checker was extracted and no v005 samples were produced. P0 and v004 completed the same short derivation check. The v005 syntax gate and closed equivalence proof passed with an empty assumption audit, but those checks do not satisfy the actual derivation requirement.']; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261121T164105Z/run-002/attempt-006/roles/inspector-9c49ebb6b9da41b8bf6e9ab2f8412d48/private-evidence/result.json |
| run-002/attempt-007 | rejected | — | — | — | — | — | inspector 제출=rejected; 응답=passed; 변경 파일=['benchmark-command.log']; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261121T164105Z/run-002/attempt-007/roles/inspector-c85afbaa367447ae839c108e0ef603f9/private-evidence/result.json |
| run-002/attempt-008 | adopted | v005 | 5.030% | +4.644 | +3.556 | 2707 | verified |
| run-002/attempt-009 | adopted | v006 | 0.000% | -0.386 | -5.030 | 50000 | verified |
| run-002/attempt-010 | adopted | v007 | 100.000% | +99.614 | +100.000 | 0 | verified |
| run-003/attempt-001 | adopted | v001 | 0.000% | -0.386 | -0.386 | 0 | verified |
| run-003/attempt-002 | rejected | — | — | — | — | — | inspector 제출=accepted; 응답=failed; 변경 파일=[]; violations=['v002 passes the shape check and its closed Coq equivalence chain has no assumptions, but the required automatic derivation fails. On the production invocation, quickchick 2 reports `convert_to_range: (dedupActsById $ acts0)` and aborts with `Failed to construct state` before extraction or any of the 10,000 sampling attempts. v002 therefore cannot be adopted or measured.']; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261121T164105Z/run-003/attempt-002/roles/inspector-097bd2ef822f48d0aa5d07da13414635/private-evidence/result.json |
| run-003/attempt-003 | rejected | — | — | — | — | — | Constructor of EnvironmentsForRequests has unexpected result: EnvironmentsForRequests s                            (@nil Spec.RequestType)                            (@nil Spec.Environment) |
| run-003/attempt-004 | rejected | — | — | — | — | — | operational_failure: ExecutionError: coordinator interrupted after confirmed generic About-output line-wrap parser defect; this frozen experiment is superseded and will not be resumed |

## 제안별 역할 비용

wall time은 해당 역할 호출 안의 도구 대기를 포함합니다. cached input과 reasoning output은 입력·출력의 부속 필드이며 중복 합산하지 않습니다. 미호출은 not_run, 실제 usage가 없으면 unavailable로 표시합니다. 검사 역할 비용은 평가 지표에 포함하지 않습니다.

| run / 제안 | 역할 | wall 초 | input | output | cached input | reasoning output | 상태 |
|---|---|---:|---:|---:|---:|---:|---|
| run-001/attempt-001 | reformulation | 237.907 | 635265 | 11779 | 608256 | 7030 | available |
| run-001/attempt-001 | proof | 109.580 | 229086 | 4752 | 209024 | 2784 | available |
| run-001/attempt-002 | reformulation | 202.889 | 514559 | 9468 | 491776 | 6385 | available |
| run-001/attempt-002 | proof | 168.630 | 689454 | 7788 | 653824 | 4059 | available |
| run-001/attempt-003 | reformulation | 140.394 | 266716 | 6916 | 232576 | 4381 | available |
| run-001/attempt-003 | proof | 102.875 | 334664 | 4674 | 300544 | 1842 | available |
| run-001/attempt-004 | reformulation | 146.580 | 452991 | 6637 | 429952 | 3685 | available |
| run-001/attempt-004 | proof | 216.691 | 721132 | 9899 | 696320 | 4705 | available |
| run-001/attempt-005 | reformulation | 114.272 | 202936 | 5652 | 176128 | 3636 | available |
| run-001/attempt-005 | proof | 215.722 | 989499 | 9521 | 956672 | 3348 | available |
| run-001/attempt-006 | reformulation | 92.696 | 274653 | 4361 | 252416 | 2451 | available |
| run-001/attempt-006 | proof | 172.909 | 539989 | 7941 | 472448 | 3210 | available |
| run-001/attempt-007 | reformulation | 124.751 | 333528 | 6003 | 308608 | 3021 | available |
| run-001/attempt-007 | proof | 236.918 | 1126292 | 10375 | 1083904 | 3559 | available |
| run-001/attempt-008 | reformulation | 132.365 | 278968 | 6026 | 251392 | 3307 | available |
| run-001/attempt-008 | proof | 366.363 | 1983635 | 16996 | 1940736 | 7653 | available |
| run-001/attempt-009 | reformulation | 138.891 | 325758 | 6739 | 297728 | 3896 | available |
| run-001/attempt-009 | proof | 437.774 | 2382582 | 20218 | 2329728 | 7529 | available |
| run-001/attempt-010 | reformulation | 111.814 | 256599 | 5416 | 217984 | 3179 | available |
| run-001/attempt-010 | proof | 358.659 | 1726941 | 16257 | 1687680 | 7081 | available |
| run-002/attempt-001 | reformulation | 132.453 | 540422 | 5566 | 506624 | 3903 | available |
| run-002/attempt-001 | proof | 62.182 | 162665 | 2704 | 147200 | 1942 | available |
| run-002/attempt-002 | reformulation | 71.569 | 173292 | 3325 | 144384 | 2369 | available |
| run-002/attempt-002 | proof | 93.265 | 286377 | 3703 | 255872 | 2434 | available |
| run-002/attempt-003 | reformulation | 207.595 | 326474 | 10487 | 307456 | 7548 | available |
| run-002/attempt-003 | proof | 105.727 | 230541 | 4276 | 216320 | 2329 | available |
| run-002/attempt-004 | reformulation | 151.156 | 256607 | 7355 | 236544 | 5211 | available |
| run-002/attempt-004 | proof | 156.444 | 771084 | 6349 | 743424 | 3387 | available |
| run-002/attempt-005 | reformulation | 111.375 | 209971 | 5511 | 191360 | 3569 | available |
| run-002/attempt-005 | proof | 105.725 | 365696 | 4804 | 331776 | 2657 | available |
| run-002/attempt-006 | reformulation | 106.574 | 199623 | 5176 | 176000 | 3558 | available |
| run-002/attempt-006 | proof | 137.017 | 481882 | 5479 | 456192 | 2770 | available |
| run-002/attempt-007 | reformulation | 99.287 | 293284 | 4136 | 258048 | 2697 | available |
| run-002/attempt-007 | proof | 134.574 | 456404 | 5262 | 435328 | 2893 | available |
| run-002/attempt-008 | reformulation | 122.720 | 275778 | 5887 | 254336 | 3691 | available |
| run-002/attempt-008 | proof | 186.767 | 532296 | 8304 | 511616 | 4364 | available |
| run-002/attempt-009 | reformulation | 137.916 | 214835 | 6606 | 192640 | 4605 | available |
| run-002/attempt-009 | proof | 151.104 | 407286 | 6771 | 385664 | 4067 | available |
| run-002/attempt-010 | reformulation | 89.116 | 342784 | 3943 | 307328 | 1979 | available |
| run-002/attempt-010 | proof | 196.044 | 841860 | 8611 | 801152 | 5037 | available |
| run-003/attempt-001 | reformulation | 59.801 | 197118 | 2616 | 180608 | 1512 | available |
| run-003/attempt-001 | proof | 74.687 | 250691 | 2982 | 205440 | 1940 | available |
| run-003/attempt-002 | reformulation | 67.644 | 266677 | 3081 | 247808 | 2066 | available |
| run-003/attempt-002 | proof | 84.492 | 255193 | 3078 | 235136 | 1754 | available |
| run-003/attempt-003 | reformulation | 128.066 | 338259 | 6230 | 316544 | 4263 | available |
| run-003/attempt-003 | proof | not_run | not_run | not_run | not_run | not_run | not_run |
| run-003/attempt-004 | reformulation | 126.951 | 309577 | 6078 | 290432 | 4392 | available |
| run-003/attempt-004 | proof | 91.226 | 260952 | 4034 | 247552 | 2509 | available |

## seed별 원시 집계

| 대상 | seed | 시도 | 확인 유효 | 확인 무효 | 결과 없음 | 판정 불가 | 확인 유효 비율 |
|---|---|---:|---:|---:|---:|---:|---:|
| P0 | 101 | 10000 | 36 | 3199 | 6107 | 658 | 0.360% |
| P0 | 202 | 10000 | 40 | 3122 | 6190 | 648 | 0.400% |
| P0 | 303 | 10000 | 40 | 3174 | 6183 | 603 | 0.400% |
| P0 | 404 | 10000 | 45 | 3195 | 6082 | 678 | 0.450% |
| P0 | 505 | 10000 | 32 | 3134 | 6162 | 672 | 0.320% |
| P0 | 합산 | 50000 | 193 | 15824 | 30724 | 3259 | 0.386% |
| run-001/v001 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-001/v001 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-001/v001 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-001/v001 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-001/v001 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-001/v001 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-001/v002 | 101 | 10000 | 9449 | 0 | 0 | 551 | 94.490% |
| run-001/v002 | 202 | 10000 | 9521 | 0 | 0 | 479 | 95.210% |
| run-001/v002 | 303 | 10000 | 9478 | 0 | 0 | 522 | 94.780% |
| run-001/v002 | 404 | 10000 | 9450 | 0 | 0 | 550 | 94.500% |
| run-001/v002 | 505 | 10000 | 9483 | 0 | 0 | 517 | 94.830% |
| run-001/v002 | 합산 | 50000 | 47381 | 0 | 0 | 2619 | 94.762% |
| run-001/v003 | 101 | 10000 | 7711 | 0 | 0 | 2289 | 77.110% |
| run-001/v003 | 202 | 10000 | 7730 | 0 | 0 | 2270 | 77.300% |
| run-001/v003 | 303 | 10000 | 7718 | 0 | 0 | 2282 | 77.180% |
| run-001/v003 | 404 | 10000 | 7735 | 0 | 0 | 2265 | 77.350% |
| run-001/v003 | 505 | 10000 | 7717 | 0 | 0 | 2283 | 77.170% |
| run-001/v003 | 합산 | 50000 | 38611 | 0 | 0 | 11389 | 77.222% |
| run-001/v004 | 101 | 10000 | 5738 | 0 | 0 | 4262 | 57.380% |
| run-001/v004 | 202 | 10000 | 5777 | 0 | 0 | 4223 | 57.770% |
| run-001/v004 | 303 | 10000 | 5749 | 0 | 0 | 4251 | 57.490% |
| run-001/v004 | 404 | 10000 | 5721 | 0 | 0 | 4279 | 57.210% |
| run-001/v004 | 505 | 10000 | 5817 | 0 | 0 | 4183 | 58.170% |
| run-001/v004 | 합산 | 50000 | 28802 | 0 | 0 | 21198 | 57.604% |
| run-001/v005 | 101 | 10000 | 2932 | 0 | 0 | 7068 | 29.320% |
| run-001/v005 | 202 | 10000 | 2934 | 0 | 0 | 7066 | 29.340% |
| run-001/v005 | 303 | 10000 | 2914 | 0 | 0 | 7086 | 29.140% |
| run-001/v005 | 404 | 10000 | 2918 | 0 | 0 | 7082 | 29.180% |
| run-001/v005 | 505 | 10000 | 2912 | 0 | 0 | 7088 | 29.120% |
| run-001/v005 | 합산 | 50000 | 14610 | 0 | 0 | 35390 | 29.220% |
| run-001/v006 | 101 | 10000 | 4774 | 0 | 0 | 5226 | 47.740% |
| run-001/v006 | 202 | 10000 | 4821 | 0 | 0 | 5179 | 48.210% |
| run-001/v006 | 303 | 10000 | 4756 | 0 | 0 | 5244 | 47.560% |
| run-001/v006 | 404 | 10000 | 4815 | 0 | 0 | 5185 | 48.150% |
| run-001/v006 | 505 | 10000 | 4815 | 0 | 0 | 5185 | 48.150% |
| run-001/v006 | 합산 | 50000 | 23981 | 0 | 0 | 26019 | 47.962% |
| run-001/v007 | 101 | 10000 | 3590 | 0 | 0 | 6410 | 35.900% |
| run-001/v007 | 202 | 10000 | 3660 | 0 | 0 | 6340 | 36.600% |
| run-001/v007 | 303 | 10000 | 3706 | 0 | 0 | 6294 | 37.060% |
| run-001/v007 | 404 | 10000 | 3736 | 0 | 0 | 6264 | 37.360% |
| run-001/v007 | 505 | 10000 | 3611 | 0 | 0 | 6389 | 36.110% |
| run-001/v007 | 합산 | 50000 | 18303 | 0 | 0 | 31697 | 36.606% |
| run-001/v008 | 101 | 10000 | 2192 | 0 | 0 | 7808 | 21.920% |
| run-001/v008 | 202 | 10000 | 2198 | 0 | 0 | 7802 | 21.980% |
| run-001/v008 | 303 | 10000 | 2178 | 0 | 0 | 7822 | 21.780% |
| run-001/v008 | 404 | 10000 | 2173 | 0 | 0 | 7827 | 21.730% |
| run-001/v008 | 505 | 10000 | 2186 | 0 | 0 | 7814 | 21.860% |
| run-001/v008 | 합산 | 50000 | 10927 | 0 | 0 | 39073 | 21.854% |
| run-002/v001 | 101 | 10000 | 34 | 2930 | 6472 | 564 | 0.340% |
| run-002/v001 | 202 | 10000 | 27 | 2824 | 6519 | 630 | 0.270% |
| run-002/v001 | 303 | 10000 | 33 | 2879 | 6507 | 581 | 0.330% |
| run-002/v001 | 404 | 10000 | 34 | 2880 | 6471 | 615 | 0.340% |
| run-002/v001 | 505 | 10000 | 25 | 2867 | 6507 | 601 | 0.250% |
| run-002/v001 | 합산 | 50000 | 153 | 14380 | 32476 | 2991 | 0.306% |
| run-002/v002 | 101 | 10000 | 595 | 8567 | 6 | 832 | 5.950% |
| run-002/v002 | 202 | 10000 | 567 | 8601 | 12 | 820 | 5.670% |
| run-002/v002 | 303 | 10000 | 579 | 8600 | 6 | 815 | 5.790% |
| run-002/v002 | 404 | 10000 | 575 | 8566 | 4 | 855 | 5.750% |
| run-002/v002 | 505 | 10000 | 615 | 8556 | 7 | 822 | 6.150% |
| run-002/v002 | 합산 | 50000 | 2931 | 42890 | 35 | 4144 | 5.862% |
| run-002/v003 | 101 | 10000 | 360 | 5209 | 4156 | 275 | 3.600% |
| run-002/v003 | 202 | 10000 | 386 | 5195 | 4097 | 322 | 3.860% |
| run-002/v003 | 303 | 10000 | 322 | 5272 | 4131 | 275 | 3.220% |
| run-002/v003 | 404 | 10000 | 375 | 5099 | 4227 | 299 | 3.750% |
| run-002/v003 | 505 | 10000 | 371 | 5187 | 4161 | 281 | 3.710% |
| run-002/v003 | 합산 | 50000 | 1814 | 25962 | 20772 | 1452 | 3.628% |
| run-002/v004 | 101 | 10000 | 151 | 2338 | 7347 | 164 | 1.510% |
| run-002/v004 | 202 | 10000 | 142 | 2374 | 7312 | 172 | 1.420% |
| run-002/v004 | 303 | 10000 | 152 | 2399 | 7287 | 162 | 1.520% |
| run-002/v004 | 404 | 10000 | 147 | 2411 | 7271 | 171 | 1.470% |
| run-002/v004 | 505 | 10000 | 145 | 2453 | 7235 | 167 | 1.450% |
| run-002/v004 | 합산 | 50000 | 737 | 11975 | 36452 | 836 | 1.474% |
| run-002/v005 | 101 | 10000 | 528 | 7171 | 1772 | 529 | 5.280% |
| run-002/v005 | 202 | 10000 | 513 | 7280 | 1661 | 546 | 5.130% |
| run-002/v005 | 303 | 10000 | 497 | 7267 | 1678 | 558 | 4.970% |
| run-002/v005 | 404 | 10000 | 486 | 7311 | 1677 | 526 | 4.860% |
| run-002/v005 | 505 | 10000 | 491 | 7291 | 1670 | 548 | 4.910% |
| run-002/v005 | 합산 | 50000 | 2515 | 36320 | 8458 | 2707 | 5.030% |
| run-002/v006 | 101 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v006 | 202 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v006 | 303 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v006 | 404 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v006 | 505 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v006 | 합산 | 50000 | 0 | 0 | 0 | 50000 | 0.000% |
| run-002/v007 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v007 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v007 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v007 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v007 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v007 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-003/v001 | 101 | 10000 | 0 | 0 | 10000 | 0 | 0.000% |
| run-003/v001 | 202 | 10000 | 0 | 0 | 10000 | 0 | 0.000% |
| run-003/v001 | 303 | 10000 | 0 | 0 | 10000 | 0 | 0.000% |
| run-003/v001 | 404 | 10000 | 0 | 0 | 10000 | 0 | 0.000% |
| run-003/v001 | 505 | 10000 | 0 | 0 | 10000 | 0 | 0.000% |
| run-003/v001 | 합산 | 50000 | 0 | 0 | 50000 | 0 | 0.000% |

## 증거

원시 역할 이벤트·usage·후보 snapshot·Coq 검사·샘플·판정: `properties/cedar_no_type_error/.runs/cedar-poc-20261121T164105Z/`. 오류의 직접 증거는 `run-003/attempt-003/syntax/resolve-v002-000.log`와 `syntax/sources/SyntaxResolve_v002_000.v`입니다.

[manifest.json](manifest.json)에 고정 commit·해시·조건, [summary.json](summary.json)에 모든 측정·실패 제안·역할 비용, [coordinator-stop.json](coordinator-stop.json)과 [operational-failure.json](operational-failure.json)에 중단 근거를 보존했습니다.

내부 QuickChick의 Passed/Gave up/Failed 요약은 각 benchmark 로그에 별도 보존됩니다. 외부 측정의 completed는 정해진 호출 수를 완료했다는 뜻이며 내부 QuickChick 테스트 통과를 뜻하지 않습니다.
