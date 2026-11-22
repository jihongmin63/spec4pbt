# Cedar predicate reformulation 결과

실험 ID: `cedar-poc-20261122T025605Z`. 상태: **완료**.

> 이 문서의 확인 유효 비율은 측정 도구의 세 결함(엔티티 목록 일반화, 같은 이름 relation 혼동, 검증기 힌트 누락)에 좌우되었습니다. 같은 후보를 고친 도구로 다시 잰 결과는 [cedar-remeasure-20261122T131403Z](../cedar-remeasure-20261122T131403Z/RESULTS.md)에 있습니다. 아래 기록은 원 실행 그대로 보존합니다.

고정 도구 commit: `bd50bbfdacbafd3ee1b47d27a954b761b0b7ebd5`. 전체 소스·도구·환경·실행 조건 해시는 [manifest.json](manifest.json)에, 원시 집계와 역할 비용은 [summary.json](summary.json)에 있습니다.

주 지표는 원본 다섯 전제가 모두 확인된 입력 수 / 전체 외부 생성 시도 수입니다. None·discard도 분모에 포함합니다. 판정 불가가 있으므로 확인된 유효 입력 비율만 보고하며 생성기 soundness/completeness나 모든 크기·seed에 대한 우위를 증명하지 않습니다.

조건: Coq 8.20.0, OCaml 4.14.2, 공식 source-hash 고정 Testing Theorems fork, 동일 quickchick 2 자동 스케줄링 경로와 지원 인스턴스, size=2, seed당 10,000회. 평가 seed는 101/202/303/404/505, 최종 미사용 seed는 1101/1202/1303/1404/1505입니다.

Reformulator·Prover는 gpt-6-sol/xhigh, Inspector는 gpt-6-sol/high의 새 격리 세션을 사용했습니다. 각 채택 후보는 직전 채택 predicate와의 닫힌 Coq 동등성 증명, 전체 prefix 검사, 독립 검사, 자동 생성 및 측정을 완료했습니다.

## 종료와 채택

| run | 제안 수 | 채택 수 | 마지막 후보 | 최고 후보 | 종료 이유 |
|---|---:|---:|---|---|---|
| run-001 | 10 | 5 | v005 | v003 | attempt_limit |
| run-002 | 10 | 9 | v009 | v004 | attempt_limit |
| run-003 | 10 | 4 | v004 | v002 | attempt_limit |

## 평가 seed의 iteration 비교

P0: 193/50,000 = **0.386%**, 판정 불가 3259회.

| run / 제안 | 판정 | 채택 | 확인 유효 비율 | P0 대비 %p | 직전 대비 %p | 판정 불가 | 사유 |
|---|---|---|---:|---:|---:|---:|---|
| run-001/attempt-001 | adopted | v001 | 0.302% | -0.084 | -0.084 | 2985 | verified |
| run-001/attempt-002 | rejected | — | — | — | — | — | inspector 제출 검사=accepted; execution_status=completed; 구조화 응답=failed; 변경 파일=; violations=['v002 fails the required official automatic scheduler derivation. Coq reports unresolved EnumSized (list EntityName) instances at Bench.v:11; no checker is extracted and no v002 attempt batch completes. P0 and v001 completed the same diagnostic derivation path.', 'The required v002 valid-input ratio and comparison cannot be measured from this snapshot. Its predicate equivalence chain compiled, passed coqchk, and was closed under the global context; those proof checks do not establish generator correctness.']; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-001/attempt-002/roles/inspector-c88ce280ecd6452ab36f1f34e087dc33/private-evidence/result.json |
| run-001/attempt-003 | adopted | v002 | 4.918% | +4.532 | +4.616 | 4301 | verified |
| run-001/attempt-004 | adopted | v003 | 99.518% | +99.132 | +94.600 | 241 | verified |
| run-001/attempt-005 | rejected | — | — | — | — | — | inspector 제출 검사=rejected; execution_status=completed; 구조화 응답=passed; 변경 파일=scripts/__pycache__/check.cpython-314.pyc, scripts/cedar/__pycache__/__init__.cpython-314.pyc, scripts/cedar/__pycache__/serialization.cpython-314.pyc, scripts/tests/__pycache__/test_cedar_validator.cpython-314.pyc; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-001/attempt-005/roles/inspector-4b2e8805fc9348fd8c04b891924495b3/private-evidence/result.json |
| run-001/attempt-006 | adopted | v004 | 4.890% | +4.504 | -94.628 | 4271 | verified |
| run-001/attempt-007 | rejected | — | — | — | — | — | prover 제출 검사=rejected; execution_status=completed; 구조화 응답=proved; 변경 파일=.Equivalence.aux, Equivalence.glob, Equivalence.v; violations=[]; 원시 사유/자기 보고=Equivalence.v proves the supplied theorem. It compiled with Coq, passed coqchk, and the frozen candidate’s hash is unchanged. |
| run-001/attempt-008 | rejected | — | — | — | — | — | inspector 제출 검사=rejected; execution_status=completed; 구조화 응답=passed; 변경 파일=scripts/__pycache__/check.cpython-314.pyc, scripts/cedar/__pycache__/__init__.cpython-314.pyc, scripts/cedar/__pycache__/serialization.cpython-314.pyc, scripts/tests/__pycache__/test_cedar_validator.cpython-314.pyc; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-001/attempt-008/roles/inspector-24ff0e2f26904d499ba91b2d3418406a/private-evidence/result.json |
| run-001/attempt-009 | rejected | — | — | — | — | — | inspector 제출 검사=rejected; execution_status=completed; 구조화 응답=passed; 변경 파일=scripts/__pycache__/check.cpython-314.pyc, scripts/cedar/__pycache__/__init__.cpython-314.pyc, scripts/cedar/__pycache__/serialization.cpython-314.pyc; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-001/attempt-009/roles/inspector-d0eb67a04de346bb96014c9e3d11f134/private-evidence/result.json |
| run-001/attempt-010 | adopted | v005 | 4.890% | +4.504 | +0.000 | 4271 | verified |
| run-002/attempt-001 | adopted | v001 | 0.302% | -0.084 | -0.084 | 2985 | verified |
| run-002/attempt-002 | adopted | v002 | 0.070% | -0.316 | -0.232 | 382 | verified |
| run-002/attempt-003 | rejected | — | — | — | — | — | prover 제출 검사=rejected; execution_status=completed; 구조화 응답=proved; 변경 파일=.Equivalence.aux, Equivalence.glob, Equivalence.v, Equivalence.vo, Equivalence.vok, Equivalence.vos; violations=[]; 원시 사유/자기 보고=Equivalence.v proves the supplied theorem. Coq compilation succeeded, and Print Assumptions reports that equivalent is closed under the global context. |
| run-002/attempt-004 | adopted | v003 | 4.138% | +3.752 | +4.068 | 2113 | verified |
| run-002/attempt-005 | adopted | v004 | 100.000% | +99.614 | +95.862 | 0 | verified |
| run-002/attempt-006 | adopted | v005 | 100.000% | +99.614 | +0.000 | 0 | verified |
| run-002/attempt-007 | adopted | v006 | 93.244% | +92.858 | -6.756 | 3378 | verified |
| run-002/attempt-008 | adopted | v007 | 99.396% | +99.010 | +6.152 | 302 | verified |
| run-002/attempt-009 | adopted | v008 | 0.000% | -0.386 | -99.396 | 50000 | verified |
| run-002/attempt-010 | adopted | v009 | 100.000% | +99.614 | +100.000 | 0 | verified |
| run-003/attempt-001 | adopted | v001 | 0.070% | -0.316 | -0.316 | 382 | verified |
| run-003/attempt-002 | rejected | — | — | — | — | — | inspector 제출 검사=rejected; execution_status=completed; 구조화 응답=passed; 변경 파일=scripts/__pycache__/check.cpython-314.pyc, scripts/cedar/__pycache__/__init__.cpython-314.pyc, scripts/cedar/__pycache__/serialization.cpython-314.pyc; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-003/attempt-002/roles/inspector-d3dd4726989240219bfe4cd77940c72c/private-evidence/result.json |
| run-003/attempt-003 | rejected | — | — | — | — | — | inspector 제출 검사=rejected; execution_status=completed; 구조화 응답=failed; 변경 파일=scripts/__pycache__/check.cpython-314.pyc, scripts/cedar/__pycache__/__init__.cpython-314.pyc, scripts/cedar/__pycache__/serialization.cpython-314.pyc; violations=['The staged equivalence chain passes Coq, coqchk, and the assumption audit, but the required run.py derivation path fails: Derived.v reports "Can\'t find: entity_names".', 'The official scheduler derives and extracts for v002, but its embedded QuickChick run gives up after 3,357 tests and 20,000 discards; it must not be reported as a passed QuickChick test. P0 also gives up.', 'The single v002 sample is proved invalid against Original because WfSchema is false. This is a measurement observation, not a proof about generator correctness; the one-attempt check does not establish the required 10,000-attempt result.']; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-003/attempt-003/roles/inspector-8338330928914febb641d312b3fd2d96/private-evidence/result.json |
| run-003/attempt-004 | rejected | — | — | — | — | — | inspector 제출 검사=accepted; execution_status=completed; 구조화 응답=failed; 변경 파일=; violations=["v002 passes the candidate-shape check and its staged Coq equivalence chain is closed with no assumptions, but automatic derivation fails. Compiling the official scheduler's Bench.v reports: “The variable ets is bound several times in pattern.” The short test-mode run produced no v002 samples; no input-validity classification or production measurement is claimed."]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-003/attempt-004/roles/inspector-5a28a18e3b3f4016a6459261dd7417b1/private-evidence/result.json |
| run-003/attempt-005 | rejected | — | — | — | — | — | prover 제출 검사=rejected; execution_status=completed; 구조화 응답=proved; 변경 파일=.Equivalence.aux, Equivalence.glob, Equivalence.v; violations=[]; 원시 사유/자기 보고=Equivalence.v proves the supplied theorem without admits or new axioms. Coq compilation succeeded using the permitted sources copied under scratch/; the frozen candidate hash matches context.json. |
| run-003/attempt-006 | adopted | v002 | 100.000% | +99.614 | +99.930 | 0 | verified |
| run-003/attempt-007 | adopted | v003 | 100.000% | +99.614 | +0.000 | 0 | verified |
| run-003/attempt-008 | rejected | — | — | — | — | — | inspector 제출 검사=rejected; execution_status=completed; 구조화 응답=passed; 변경 파일=scripts/tests/__pycache__/test_cedar_validator.cpython-314.pyc; violations=[]; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-003/attempt-008/roles/inspector-b4666cefb74548dfa722f81a93a31b8c/private-evidence/result.json |
| run-003/attempt-009 | rejected | — | — | — | — | — | inspector 제출 검사=accepted; execution_status=completed; 구조화 응답=failed; 변경 파일=; violations=['The documented scripts/run.py derivation path fails for v004: Coq reports “No Checkers or Producers for relation: TypedExpr.” The closed equivalence chain, syntax gate, and official scheduler test-mode derivation passed. One generated input was validated against all five original premises; this sampling does not prove generator correctness.']; 원시 사유/자기 보고=independent inspection did not pass: /workspace/spec4pbt/properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/run-003/attempt-009/roles/inspector-dd70bc23e93d4ba091e67c37682d0342/private-evidence/result.json |
| run-003/attempt-010 | adopted | v004 | 86.102% | +85.716 | -13.898 | 6949 | verified |

## 제안별 역할 비용

wall time은 해당 역할 호출 시작부터 종료까지이며 내부 도구 대기를 포함합니다. 입력·출력 토큰은 실제 usage입니다. cached input과 reasoning output은 각각 입력·출력의 부속 필드이므로 더하지 않습니다. 미호출은 not_run, 누락된 usage는 unavailable로 남깁니다.

| run / 제안 | 역할 | wall 초 | input | output | cached input | reasoning output | 상태 |
|---|---|---:|---:|---:|---:|---:|---|
| run-001/attempt-001 | reformulation | 78.592 | 267168 | 3355 | 246272 | 2250 | available |
| run-001/attempt-001 | proof | 60.456 | 244668 | 2437 | 229376 | 1476 | available |
| run-001/attempt-002 | reformulation | 126.595 | 242364 | 6258 | 224000 | 4927 | available |
| run-001/attempt-002 | proof | 138.979 | 574059 | 5454 | 547328 | 2772 | available |
| run-001/attempt-003 | reformulation | 213.641 | 965927 | 9602 | 936576 | 6628 | available |
| run-001/attempt-003 | proof | 84.277 | 222044 | 3854 | 189312 | 2574 | available |
| run-001/attempt-004 | reformulation | 249.904 | 654034 | 12347 | 629248 | 8348 | available |
| run-001/attempt-004 | proof | 150.347 | 226251 | 7008 | 207616 | 4580 | available |
| run-001/attempt-005 | reformulation | 138.619 | 274009 | 6843 | 250624 | 4354 | available |
| run-001/attempt-005 | proof | 127.357 | 389202 | 6025 | 356992 | 2611 | available |
| run-001/attempt-006 | reformulation | 96.499 | 301593 | 4483 | 277248 | 2767 | available |
| run-001/attempt-006 | proof | 126.574 | 487066 | 5229 | 467456 | 2790 | available |
| run-001/attempt-007 | reformulation | 110.813 | 215787 | 5223 | 195712 | 3439 | available |
| run-001/attempt-007 | proof | 117.745 | 375311 | 4881 | 352640 | 2584 | available |
| run-001/attempt-008 | reformulation | 80.218 | 263197 | 3528 | 240128 | 2156 | available |
| run-001/attempt-008 | proof | 110.075 | 375137 | 4924 | 345088 | 2674 | available |
| run-001/attempt-009 | reformulation | 92.592 | 301024 | 4229 | 263680 | 2244 | available |
| run-001/attempt-009 | proof | 122.477 | 366320 | 5253 | 328448 | 2806 | available |
| run-001/attempt-010 | reformulation | 82.941 | 214267 | 3798 | 193792 | 2495 | available |
| run-001/attempt-010 | proof | 97.894 | 309154 | 4422 | 276224 | 2535 | available |
| run-002/attempt-001 | reformulation | 103.742 | 311577 | 4841 | 291712 | 3234 | available |
| run-002/attempt-001 | proof | 90.888 | 275569 | 3874 | 259456 | 2622 | available |
| run-002/attempt-002 | reformulation | 103.933 | 374944 | 4231 | 352768 | 2803 | available |
| run-002/attempt-002 | proof | 81.051 | 309258 | 2932 | 291968 | 1556 | available |
| run-002/attempt-003 | reformulation | 164.039 | 281037 | 7984 | 251520 | 6309 | available |
| run-002/attempt-003 | proof | 79.722 | 236812 | 3716 | 221184 | 2191 | available |
| run-002/attempt-004 | reformulation | 73.751 | 173043 | 3053 | 156288 | 2082 | available |
| run-002/attempt-004 | proof | 87.689 | 279168 | 3293 | 257792 | 1869 | available |
| run-002/attempt-005 | reformulation | 189.026 | 263297 | 9147 | 244224 | 6904 | available |
| run-002/attempt-005 | proof | 135.662 | 346931 | 5992 | 306560 | 3855 | available |
| run-002/attempt-006 | reformulation | 77.457 | 189248 | 3579 | 169984 | 2263 | available |
| run-002/attempt-006 | proof | 155.971 | 546983 | 6630 | 511616 | 4204 | available |
| run-002/attempt-007 | reformulation | 84.642 | 251008 | 3778 | 227584 | 2469 | available |
| run-002/attempt-007 | proof | 173.488 | 404641 | 7719 | 383104 | 3647 | available |
| run-002/attempt-008 | reformulation | 108.163 | 270695 | 4775 | 249984 | 3397 | available |
| run-002/attempt-008 | proof | 154.793 | 605031 | 6586 | 583680 | 3582 | available |
| run-002/attempt-009 | reformulation | 92.974 | 225853 | 3851 | 203648 | 2595 | available |
| run-002/attempt-009 | proof | 136.637 | 391320 | 6546 | 358784 | 4196 | available |
| run-002/attempt-010 | reformulation | 86.499 | 243691 | 3572 | 218112 | 2222 | available |
| run-002/attempt-010 | proof | 141.549 | 457294 | 5918 | 432256 | 2738 | available |
| run-003/attempt-001 | reformulation | 61.799 | 175584 | 2794 | 157184 | 1857 | available |
| run-003/attempt-001 | proof | 76.964 | 341599 | 3041 | 322560 | 1793 | available |
| run-003/attempt-002 | reformulation | 75.634 | 269069 | 3322 | 249984 | 1998 | available |
| run-003/attempt-002 | proof | 82.115 | 273140 | 3634 | 256128 | 2169 | available |
| run-003/attempt-003 | reformulation | 72.478 | 236368 | 3230 | 214912 | 2161 | available |
| run-003/attempt-003 | proof | 79.553 | 453229 | 3167 | 433152 | 1488 | available |
| run-003/attempt-004 | reformulation | 117.541 | 314270 | 5677 | 294528 | 4110 | available |
| run-003/attempt-004 | proof | 94.771 | 273826 | 3812 | 256000 | 2535 | available |
| run-003/attempt-005 | reformulation | 122.299 | 284394 | 5909 | 264320 | 4333 | available |
| run-003/attempt-005 | proof | 69.727 | 205224 | 2977 | 189824 | 1818 | available |
| run-003/attempt-006 | reformulation | 180.527 | 658702 | 8422 | 637184 | 6043 | available |
| run-003/attempt-006 | proof | 99.698 | 385039 | 3889 | 339200 | 2122 | available |
| run-003/attempt-007 | reformulation | 117.464 | 234019 | 5067 | 203648 | 3575 | available |
| run-003/attempt-007 | proof | 145.661 | 357545 | 6501 | 334336 | 3848 | available |
| run-003/attempt-008 | reformulation | 140.101 | 425820 | 6527 | 396928 | 4130 | available |
| run-003/attempt-008 | proof | 191.457 | 857532 | 7470 | 833152 | 3879 | available |
| run-003/attempt-009 | reformulation | 110.756 | 216806 | 5464 | 197376 | 3683 | available |
| run-003/attempt-009 | proof | 166.862 | 629228 | 6729 | 602624 | 2696 | available |
| run-003/attempt-010 | reformulation | 116.096 | 257664 | 5602 | 237184 | 3431 | available |
| run-003/attempt-010 | proof | 140.946 | 585692 | 6335 | 532352 | 3244 | available |

## 평가 seed별 집계

| 대상 | seed | 시도 | 확인 유효 | 확인 무효 | 결과 없음 | 판정 불가 | 확인 유효 비율 |
|---|---|---:|---:|---:|---:|---:|---:|
| P0 | 101 | 10000 | 36 | 3199 | 6107 | 658 | 0.360% |
| P0 | 202 | 10000 | 40 | 3122 | 6190 | 648 | 0.400% |
| P0 | 303 | 10000 | 40 | 3174 | 6183 | 603 | 0.400% |
| P0 | 404 | 10000 | 45 | 3195 | 6082 | 678 | 0.450% |
| P0 | 505 | 10000 | 32 | 3134 | 6162 | 672 | 0.320% |
| P0 | 합산 | 50000 | 193 | 15824 | 30724 | 3259 | 0.386% |
| run-001/v001 | 101 | 10000 | 29 | 2866 | 6539 | 566 | 0.290% |
| run-001/v001 | 202 | 10000 | 31 | 2929 | 6420 | 620 | 0.310% |
| run-001/v001 | 303 | 10000 | 28 | 2880 | 6483 | 609 | 0.280% |
| run-001/v001 | 404 | 10000 | 37 | 2893 | 6482 | 588 | 0.370% |
| run-001/v001 | 505 | 10000 | 26 | 2934 | 6438 | 602 | 0.260% |
| run-001/v001 | 합산 | 50000 | 151 | 14502 | 32362 | 2985 | 0.302% |
| run-001/v002 | 101 | 10000 | 508 | 8238 | 399 | 855 | 5.080% |
| run-001/v002 | 202 | 10000 | 520 | 8169 | 409 | 902 | 5.200% |
| run-001/v002 | 303 | 10000 | 483 | 8290 | 392 | 835 | 4.830% |
| run-001/v002 | 404 | 10000 | 488 | 8219 | 419 | 874 | 4.880% |
| run-001/v002 | 505 | 10000 | 460 | 8300 | 405 | 835 | 4.600% |
| run-001/v002 | 합산 | 50000 | 2459 | 41216 | 2024 | 4301 | 4.918% |
| run-001/v003 | 101 | 10000 | 9947 | 0 | 0 | 53 | 99.470% |
| run-001/v003 | 202 | 10000 | 9952 | 0 | 0 | 48 | 99.520% |
| run-001/v003 | 303 | 10000 | 9949 | 0 | 0 | 51 | 99.490% |
| run-001/v003 | 404 | 10000 | 9952 | 0 | 0 | 48 | 99.520% |
| run-001/v003 | 505 | 10000 | 9959 | 0 | 0 | 41 | 99.590% |
| run-001/v003 | 합산 | 50000 | 49759 | 0 | 0 | 241 | 99.518% |
| run-001/v004 | 101 | 10000 | 487 | 8296 | 373 | 844 | 4.870% |
| run-001/v004 | 202 | 10000 | 492 | 8266 | 373 | 869 | 4.920% |
| run-001/v004 | 303 | 10000 | 541 | 8165 | 424 | 870 | 5.410% |
| run-001/v004 | 404 | 10000 | 454 | 8342 | 383 | 821 | 4.540% |
| run-001/v004 | 505 | 10000 | 471 | 8232 | 430 | 867 | 4.710% |
| run-001/v004 | 합산 | 50000 | 2445 | 41301 | 1983 | 4271 | 4.890% |
| run-001/v005 | 101 | 10000 | 487 | 8296 | 373 | 844 | 4.870% |
| run-001/v005 | 202 | 10000 | 492 | 8266 | 373 | 869 | 4.920% |
| run-001/v005 | 303 | 10000 | 541 | 8165 | 424 | 870 | 5.410% |
| run-001/v005 | 404 | 10000 | 454 | 8342 | 383 | 821 | 4.540% |
| run-001/v005 | 505 | 10000 | 471 | 8232 | 430 | 867 | 4.710% |
| run-001/v005 | 합산 | 50000 | 2445 | 41301 | 1983 | 4271 | 4.890% |
| run-002/v001 | 101 | 10000 | 29 | 2866 | 6539 | 566 | 0.290% |
| run-002/v001 | 202 | 10000 | 31 | 2929 | 6420 | 620 | 0.310% |
| run-002/v001 | 303 | 10000 | 28 | 2880 | 6483 | 609 | 0.280% |
| run-002/v001 | 404 | 10000 | 37 | 2893 | 6482 | 588 | 0.370% |
| run-002/v001 | 505 | 10000 | 26 | 2934 | 6438 | 602 | 0.260% |
| run-002/v001 | 합산 | 50000 | 151 | 14502 | 32362 | 2985 | 0.302% |
| run-002/v002 | 101 | 10000 | 8 | 389 | 9521 | 82 | 0.080% |
| run-002/v002 | 202 | 10000 | 10 | 393 | 9525 | 72 | 0.100% |
| run-002/v002 | 303 | 10000 | 3 | 401 | 9514 | 82 | 0.030% |
| run-002/v002 | 404 | 10000 | 8 | 386 | 9521 | 85 | 0.080% |
| run-002/v002 | 505 | 10000 | 6 | 391 | 9542 | 61 | 0.060% |
| run-002/v002 | 합산 | 50000 | 35 | 1960 | 47623 | 382 | 0.070% |
| run-002/v003 | 101 | 10000 | 447 | 5776 | 3295 | 482 | 4.470% |
| run-002/v003 | 202 | 10000 | 381 | 5810 | 3400 | 409 | 3.810% |
| run-002/v003 | 303 | 10000 | 403 | 5921 | 3239 | 437 | 4.030% |
| run-002/v003 | 404 | 10000 | 388 | 5939 | 3285 | 388 | 3.880% |
| run-002/v003 | 505 | 10000 | 450 | 5870 | 3283 | 397 | 4.500% |
| run-002/v003 | 합산 | 50000 | 2069 | 29316 | 16502 | 2113 | 4.138% |
| run-002/v004 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v004 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v004 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v004 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v004 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v004 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-002/v005 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v005 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v005 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v005 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v005 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v005 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-002/v006 | 101 | 10000 | 9326 | 0 | 0 | 674 | 93.260% |
| run-002/v006 | 202 | 10000 | 9329 | 0 | 0 | 671 | 93.290% |
| run-002/v006 | 303 | 10000 | 9318 | 0 | 0 | 682 | 93.180% |
| run-002/v006 | 404 | 10000 | 9336 | 0 | 0 | 664 | 93.360% |
| run-002/v006 | 505 | 10000 | 9313 | 0 | 0 | 687 | 93.130% |
| run-002/v006 | 합산 | 50000 | 46622 | 0 | 0 | 3378 | 93.244% |
| run-002/v007 | 101 | 10000 | 9939 | 0 | 0 | 61 | 99.390% |
| run-002/v007 | 202 | 10000 | 9946 | 0 | 0 | 54 | 99.460% |
| run-002/v007 | 303 | 10000 | 9938 | 0 | 0 | 62 | 99.380% |
| run-002/v007 | 404 | 10000 | 9942 | 0 | 0 | 58 | 99.420% |
| run-002/v007 | 505 | 10000 | 9933 | 0 | 0 | 67 | 99.330% |
| run-002/v007 | 합산 | 50000 | 49698 | 0 | 0 | 302 | 99.396% |
| run-002/v008 | 101 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v008 | 202 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v008 | 303 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v008 | 404 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v008 | 505 | 10000 | 0 | 0 | 0 | 10000 | 0.000% |
| run-002/v008 | 합산 | 50000 | 0 | 0 | 0 | 50000 | 0.000% |
| run-002/v009 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-003/v001 | 101 | 10000 | 8 | 389 | 9521 | 82 | 0.080% |
| run-003/v001 | 202 | 10000 | 10 | 393 | 9525 | 72 | 0.100% |
| run-003/v001 | 303 | 10000 | 3 | 401 | 9514 | 82 | 0.030% |
| run-003/v001 | 404 | 10000 | 8 | 386 | 9521 | 85 | 0.080% |
| run-003/v001 | 505 | 10000 | 6 | 391 | 9542 | 61 | 0.060% |
| run-003/v001 | 합산 | 50000 | 35 | 1960 | 47623 | 382 | 0.070% |
| run-003/v002 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v002 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v002 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v002 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v002 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v002 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-003/v003 | 101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v003 | 202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v003 | 303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v003 | 404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v003 | 505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-003/v003 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-003/v004 | 101 | 10000 | 8654 | 0 | 0 | 1346 | 86.540% |
| run-003/v004 | 202 | 10000 | 8624 | 0 | 0 | 1376 | 86.240% |
| run-003/v004 | 303 | 10000 | 8556 | 0 | 0 | 1444 | 85.560% |
| run-003/v004 | 404 | 10000 | 8596 | 0 | 0 | 1404 | 85.960% |
| run-003/v004 | 505 | 10000 | 8621 | 0 | 0 | 1379 | 86.210% |
| run-003/v004 | 합산 | 50000 | 43051 | 0 | 0 | 6949 | 86.102% |

## 최종 미사용 seed 비교

모든 run이 종료된 후 P0와 각 run의 마지막 채택 후보를 재평가했습니다. 이 결과는 worker 피드백으로 전달하지 않았습니다.

| 대상 | 확인 유효 비율 | P0 대비 %p | 판정 불가 |
|---|---:|---:|---:|
| P0 | 0.280% | — | 3229 |
| run-001/v005 | 4.966% | +4.686 | 4268 |
| run-002/v009 | 100.000% | +99.720 | 0 |
| run-003/v004 | 86.136% | +85.856 | 6932 |

## 미사용 seed별 집계

| 대상 | seed | 시도 | 확인 유효 | 확인 무효 | 결과 없음 | 판정 불가 | 확인 유효 비율 |
|---|---|---:|---:|---:|---:|---:|---:|
| P0 | 1101 | 10000 | 23 | 3164 | 6156 | 657 | 0.230% |
| P0 | 1202 | 10000 | 32 | 3168 | 6152 | 648 | 0.320% |
| P0 | 1303 | 10000 | 29 | 3198 | 6128 | 645 | 0.290% |
| P0 | 1404 | 10000 | 34 | 3170 | 6174 | 622 | 0.340% |
| P0 | 1505 | 10000 | 22 | 3255 | 6066 | 657 | 0.220% |
| P0 | 합산 | 50000 | 140 | 15955 | 30676 | 3229 | 0.280% |
| run-001/v005 | 1101 | 10000 | 512 | 8233 | 394 | 861 | 5.120% |
| run-001/v005 | 1202 | 10000 | 471 | 8305 | 397 | 827 | 4.710% |
| run-001/v005 | 1303 | 10000 | 483 | 8260 | 408 | 849 | 4.830% |
| run-001/v005 | 1404 | 10000 | 516 | 8229 | 389 | 866 | 5.160% |
| run-001/v005 | 1505 | 10000 | 501 | 8268 | 366 | 865 | 5.010% |
| run-001/v005 | 합산 | 50000 | 2483 | 41295 | 1954 | 4268 | 4.966% |
| run-002/v009 | 1101 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 1202 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 1303 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 1404 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 1505 | 10000 | 10000 | 0 | 0 | 0 | 100.000% |
| run-002/v009 | 합산 | 50000 | 50000 | 0 | 0 | 0 | 100.000% |
| run-003/v004 | 1101 | 10000 | 8515 | 0 | 0 | 1485 | 85.150% |
| run-003/v004 | 1202 | 10000 | 8646 | 0 | 0 | 1354 | 86.460% |
| run-003/v004 | 1303 | 10000 | 8599 | 0 | 0 | 1401 | 85.990% |
| run-003/v004 | 1404 | 10000 | 8676 | 0 | 0 | 1324 | 86.760% |
| run-003/v004 | 1505 | 10000 | 8632 | 0 | 0 | 1368 | 86.320% |
| run-003/v004 | 합산 | 50000 | 43068 | 0 | 0 | 6932 | 86.136% |

## 해석과 검사의 한계

채택은 성능 향상을 보장하지 않았습니다. run-001은 최고 후보 v003 이후 마지막 v005의 평가 비율이 낮아졌고, run-003도 최고 v002/v003의 100%에서 마지막 v004의 86.102%로 낮아졌습니다. 마지막 후보를 기준으로 미사용 seed 평가를 수행했으며 최고 후보로 교체하지 않았습니다.

run-002 v008의 확인 유효 비율 0%는 50,000회 모두 판정 불가였다는 뜻입니다. 확인 무효 50,000회라는 뜻이 아닙니다. 제한된 validator가 확인하지 못한 입력을 무효로 합산하지 않았습니다.

실제 탐색 경로에는 역할 제출 거부도 영향을 주었습니다. scratch 밖 Python 캐시 또는 Coq 생성 파일을 남긴 제출은 파일 변경 계약에 따라 거부했습니다. 이 경우 증명/검사 응답의 proved 또는 passed와 제출 거부를 구분했습니다.

run-003 attempt-009는 Inspector가 구형 scripts/run.py의 도출 실패만을 근거로 failed를 반환하여 탈락했습니다. 같은 응답은 공식 scheduler 도출, 문법 및 닫힌 동치 증명이 통과했다고 명시합니다. 따라서 이 탈락은 선택한 공식 benchmark 경로의 실패나 predicate 비동등성을 입증하지 않으며, 독립 검사 agent의 기준 적용 오류가 탐색에 미친 한계로 남깁니다. attempt-003의 구형 경로 오류·내부 gave_up·단일 무효 샘플 관련 주장도 공식 경로의 실패 판정으로 일반화하지 않습니다. 모든 실제 판정과 비용은 변경 없이 보존했습니다.

완료 후 [final-audit.json](final-audit.json)에서 동결 commit·소스·조건의 불변성, 30개 제안의 역할 비용과 실제 호출 모델/effort, fresh 세션 구분, 채택 증명·후보와 검증 snapshot의 바이트 일치를 확인했습니다. 조정 세션의 모델·effort는 이 대화에서 선택·변경할 수 없어 권장값 적용을 주장하지 않습니다.

최종 환경 검사 bash environment/env.sh check는 종료 코드 0, 10,000회 테스트 5개 모두 Passed(0 discards), 도출·실행·커널 검사 성공을 확인했습니다. 증거는 _opam-testing-theorems/checks/verification.wM61BPNA 및 _opam-testing-theorems/checks/cedar-poc-20261122T025605Z-final-check.log에 있습니다. 도구 동결 전 회귀검사 87개와 새 독립 도구 검사 세션의 87개 검사도 통과했습니다.


## 재현과 증거

동일 commit에서 [도구 독립 검사 절차](../../../../scripts/cedar/README.md)에 따라 새 review를 만든 뒤, 사용하지 않은 실험 ID로 실행합니다.

```sh
python3 scripts/cedar/execute.py --experiment-id cedar-NEW-ID --tool-review properties/cedar_no_type_error/.runs/NEW-REVIEW/review.json
```

실제 실행의 역할별 snapshot·원시 이벤트·usage·검사·샘플·판정은 `properties/cedar_no_type_error/.runs/cedar-poc-20261122T025605Z/`에 보존됩니다. 실패한 제안은 이 비공개 증거에 남으며 채택 체인에 포함되지 않습니다.

각 마지막 후보의 미사용 seed 원시 benchmark·샘플·판정은 `properties/cedar_no_type_error/experiments/cedar-poc-20261122T025605Z/run-NNN/.runs/benchmark-vNNN-SEED/`에 보존됩니다. 상위 실험 증거의 held-out/run-NNN 명령 로그가 이 경로를 참조하며, 이 중첩 .runs 데이터는 버전 관리에서 제외됩니다.

내부 QuickChick의 Passed/Gave up/Failed와 실제 카운터는 각 benchmark result.json 및 scheduler.log에 운영 증거로 보존합니다. benchmark의 completed는 자동 도출과 정해진 외부 시도 완료를 뜻하며 내부 QuickChick 테스트 통과 주장과 구분합니다.

이전 중단 실행 cedar-poc-20261121T134241Z, cedar-poc-20261121T141829Z, cedar-poc-20261121T153402Z 및 cedar-poc-20261121T164105Z의 상태·측정·비용은 각 STATUS.md와 summary.json에 별도 보존했습니다. 이 실험에는 이전 측정·후보·피드백을 재사용하지 않았습니다.
