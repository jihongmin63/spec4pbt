# Predicate reformulation

Coq + QuickChick의 생성기 및 정확성 증명 자동 도출을 위한 독립 환경이다.
환경 설정은 `environment/`의 두 파일로 관리한다.

```text
environment/
├── env.sh                  # 설치·실행·검증 통합 스크립트
└── opam-switch.export      # 패키지 버전·소스·체크섬 고정
example.v                   # 생성기와 정확성 증명 자동 도출 예제
specification/              # 명세 작성 공간
properties/                 # 속성 작성 공간
adapters/                   # 어댑터 작성 공간
```

세 작업 폴더에는 Git에서 빈 디렉터리를 유지하기 위한 `.gitkeep`만 둔다.

## 버전

| 구성 요소 | 고정 버전 |
| --- | --- |
| Coq (Rocq의 이전 이름) | 8.6.1 |
| QuickChick | `popl-ifc-eval`, 로컬 패키지 `0.0.0+popl2018` |
| OCaml | 4.05.0 |
| MathComp ssreflect | 1.6.4 |
| Camlp5 | 7.14 |
| ocamlbuild | 0.14.3 |
| ocamlfind | 1.9.6 |

QuickChick 소스는 `f2b2fc64bd2ca81ef677d9bb6f36d8ee0adb6217`로 고정한다.
`0.0.0+popl2018`은 재현을 위한 로컬 패키지 이름이며 공식 릴리스 번호가 아니다.
최신 버전보다 생성기와 soundness/completeness 증명의 자동 도출을 기준으로
선택했다. QuickChick 소스는 수정하지 않는다.

## 설치와 사용

검증된 플랫폼은 Linux x86_64다. Git, opam, make, `/usr/bin/gcc`, Perl과
네트워크가 필요하다. 시스템 도구는 미리 설치해야 하며, opam을 처음 쓰는
환경에서는 다음 명령으로 초기화한다.

```sh
opam init --bare --disable-shell-hook --yes
```

이 브랜치의 checkout 루트에서 실행한다.

```sh
bash environment/env.sh setup                  # 환경 설치·복원
bash environment/env.sh check                  # 자동 증명·실행·커널 검사
bash environment/env.sh coqtop                 # 대화형 Coq
bash environment/env.sh coqc MyExperiment.v    # 자신의 파일 컴파일
```

설치 스크립트는 checkout 내부의 `_opam-popl18/`에 전용 opam switch를
구성한다. 같은 설치 명령을 다시 실행할 수 있으며, 빌드 병렬도는
`JOBS=2 bash environment/env.sh setup`처럼 조절한다(기본 8).
필요한 저장소를 공유 opam 목록에 등록하지만 다른 switch의 패키지나
저장소 선택, 전역 switch와 shell 설정은 바꾸지 않는다.

Coq/OCaml 구버전 의존성은 공식 opam 보관 저장소를 사용한다. GCC 호환
래퍼는 설치 폴더 안에 자동 생성하며, C11 모드와
`-Wno-implicit-function-declaration` 옵션을 적용한다.
패키지 메타데이터는 고정 파일에 포함돼 있으므로 별도 로컬 저장소는 필요 없다.

## 검증 범위

`example.v`는 짝수 관계에서 생성기와 정확성 증명을 자동 도출한다.
정확성 정리는 다음 동치를 뜻한다.

```text
Some n이 생성기의 가능한 출력이다 ↔ Even n
```

soundness는 왼쪽에서 오른쪽, completeness는 오른쪽에서 왼쪽이다.
가능한 출력은 모든 크기와 난수 seed에 걸친 의미이며, 유한 실행이 모든
짝수를 생성한다는 뜻은 아니다. 지원되는 predicate마다 자동 도출 여부를
별도로 확인해야 한다.

`check`는 자동 증명 도출, 10,000회 실행 검사, `coqchk` 커널 검사를 수행한다.
검증마다 `_opam-popl18/checks/verification.*/`에 새 로그를 남기며 이전 결과는
지우지 않는다. 설치물과 검증 결과는 Git에서 제외한다.

이 예제의 `Print Assumptions`에는 `RandomSeed`, `randomSplit`,
`randomSplitAssumption`, `randomSeed_inhabited`, `randomRNat`,
`ramdomRNatCorrect`가 나타난다. 이는 QuickChick의 난수 모델 가정이다.
예제에 `Admitted`나 새로운 `Axiom`을 추가하지 않으며, upstream의 미완성
보조정리는 이 예제의 정확성 증명에 포함되지 않는다.
