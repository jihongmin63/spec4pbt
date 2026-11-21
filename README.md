# Predicate reformulation / Cedar experiments

`cedar-experiments`는 `predicate-reformulation`에서 분기한 실험 브랜치다.
*Testing Theorems, Fully Automatically*의 공식 소스 아티팩트 환경을 사용한다.
생성기 정확성 증명은 제외하고 **predicate 동등성 증명은 유지**한다.

[Cedar 명세](specification/cedar/README.md)는 `specification/cedar/Spec.v`에,
[생성 전제와 성질](properties/cedar_no_type_error/README.md)은
`properties/cedar_no_type_error/Original.v`에 있다. 원본 아티팩트도 보존한다.

[실험 실행 프롬프트](prompts/cedar-experiments.txt)는 Testing Theorems와의 비교,
역할별 모델 설정, 매 호출의 context 격리, 측정·종료 조건을 정리한다.

## 환경

| 구성 요소 | 버전 |
| --- | --- |
| Coq | 8.20.0 |
| OCaml | 4.14.2 |
| QuickChick | 공식 Testing Theorems 아티팩트 fork (`dev`) |
| MathComp ssreflect | 1.19.0 |
| ExtLib / SimpleIO | 0.13.2 / 1.11.0 |
| Cedar Rust 라이브러리 | 4.8.2 (`Cargo.lock`) |

QuickChick은 일반 배포판 2.2.0과 다르다. 공식 Dockerfile과 같은 Coq·OCaml,
동일한 QuickChick 소스를 네이티브로 빌드했다. Docker 이미지 전체를 복원한 것은 아니다.
의존성 버전·메타데이터는 `environment/opam-switch.export`에 고정한다.
QuickChick 소스는 수정하지 않으며, Dockerfile과 같이 예제의 dune 파일만 비활성화한다.

- [논문](https://lemonidas.github.io/pdf/TestingTheorems.pdf)
- [공식 아티팩트](https://zenodo.org/records/22087774)
- 안쪽 소스 아카이브 SHA-256:
  `876e30bf41477f9a90077e3876df08555c77b624b35e11508500f4ae01e7035a`

## 설치와 실행

Linux x86_64, Python 3, opam, C 빌드 도구, curl, GMP와 네트워크가 필요하다.
설치물·캐시·로그는 `_opam-testing-theorems/`에 둔다. 다른 worktree와 기존 switch는 보존한다.
opam 초기 설정이 없다면 `opam init --bare --disable-shell-hook --yes`를 먼저 실행한다.

```sh
bash environment/env.sh setup          # Coq 및 논문 QuickChick 설치
bash environment/env.sh setup-cedar    # 공식 Cedar 서버 빌드 (별도 Rust nightly)
bash environment/env.sh check          # 2018·2022·2023·2026 기능 및 실행 검사
bash environment/env.sh check-cedar    # 원본 성질을 실제 Cedar 서버와 차등 검사
bash environment/env.sh coqtop
bash environment/env.sh coqc MyExperiment.v
```

`JOBS=2` 등으로 빌드 병렬도를 바꿀 수 있다. 최초 설치는 공식 배포 파일에서
27 MB 소스 아카이브를 스트리밍으로 꺼내 체크섬을 확인한다. 이후에는 캐시를 사용한다.
Rust nightly는 아티팩트 Dockerfile과 같이 설치 시점 버전이며 Cargo 의존성은 잠겨 있다.

## 실행 확인 (2026-11-21)

| 대상 | 실제 검사 | 결과 |
| --- | --- | --- |
| 2018 Generating Good Generators | `ArbitrarySizedSuchThat`, 짝수 생성 | 10,000회 통과, discard 0 |
| 2022 Computing Correctly | `DecOpt`, 생성, 열거 | 짝수/홀수 판정·열거 결과 확인, 생성 10,000회 통과 |
| 2023 Merging Inductive Relations | Even과 Three 병합 후 생성 | 6의 배수 검사 10,000회 통과, discard 0 |
| 2026 Testing Theorems | 자동 스케줄링 | 작은 예제 및 원본 Cedar 실행 |
| 2026 Cedar 원본 | `quickchick 2.` + Cedar 4.8.2 서버 | 10,000회 통과, discard 2,386, 테스트 시간 4.677초 |
| 기존 property workflow | 실제 Coq 회귀검사 | 14개 통과 |

구형 연구의 행은 현재 fork에 남아 있는 핵심 기능을 실행한 결과이며,
각 논문의 전체 실험이나 Cedar 전체에 대한 성공을 뜻하지 않는다.
Cedar에서는 구형 `Derive DecOpt`가 `LookupEntityAttr`에 대해
`Pattern "_" is redundant in this clause`로 실패한다. 같은 관계의 구형 생성·열거도
`No Classes found`로 실패했고, `WfCedarType`과 `HasType`의 직접 병합은 `Failure("Not")`로 실패했다.
**버전 변경만으로 구형 방식의 Cedar 전체 baseline이 완성되지는 않는다.**

2026 방식은 원본 명세·성질·직렬화·Cedar 서버를 그대로 사용했다.
10,000 / 12,386 ≈ 80.7%는 이번 실행에서 discard되지 않고 통과한 비율이다.
생성기의 형식적 정확성, 독립적인 모든 전제 재검사, 다양성 측정이나 성능 우위는 입증하지 않는다.
테스트 시간은 도출·컴파일 시간을 제외하며, 고정 seed의 성능 benchmark도 아니다.
원본 `Admitted`는 테스트가 끝난 conjecture이며 증명으로 취급하지 않는다.

검사 예제는 `environment/checks/`에 있다. 실행 로그는 아래에 보존했다.

- Cedar: `_opam-testing-theorems/checks/cedar.uJ7gh2PI/`
- 구형 Cedar 실패 재현: `properties/cedar_no_type_error/.runs/artifact-legacy-cedar.u240ot0b/`
- workflow: `_opam-testing-theorems/workflow-regression.log`
- 기능 검사: `_opam-testing-theorems/method-check-final.log`

## Property 변환 탐색

property마다 원본과 순서가 있는 후보를 다음처럼 둔다. 설정 JSON이나
직접 작성하는 `Generator.v`는 필요 없다.

```text
specification/<spec-name>/Spec.v
properties/<name>/
├── Original.v
└── candidates/
    ├── v001/
    │   ├── Candidate.v
    │   └── Equivalence.v
    └── v002/
        ├── Candidate.v
        └── Equivalence.v
```

`Original.v`는 `Input : Type`과 `predicate : Input -> Prop`를 제공한다.
생성 조건에 여러 값이 필요하면 `Input`을 record나 tuple로 정의한다.
`Candidate.v`는 동일한 입력 타입의 `predicate`를 정의한다. 생성 대상 후보는
`Inductive` 관계로 작성하고, 새 관계의 각 premise는 귀납 관계의 적용이어야 한다.
conjunction은 여러 premise로, disjunction은 여러 constructor로, existential은
constructor의 변수로 표현한다. 임의 함수·Boolean 조건을 귀납 wrapper로 감싸
이 제약을 우회하지 않는다. 고정된 명세와 `Original.v`에는 이 문법 제한을
소급 적용하지 않는다. 실제 도출 성공도 실행 전에 확인한다.

명세는 `Specification.<spec-name>.Spec`, 원본은 `Property.Original`,
후보는 `Property.candidates.v001.Candidate`처럼 import한다. 명세 폴더와
파일명은 Coq 식별자로 쓴다. 예를 들어 폴더명에는 `-` 대신 `_`를 사용한다.

첫 번째 `Equivalence.v`는 다음 인터페이스의 정리를 완성해야 한다.

```coq
Require Property.Original Property.candidates.v001.Candidate.

Theorem equivalent : forall x : Property.Original.Input,
  Property.Original.predicate x <->
  Property.candidates.v001.Candidate.predicate x.
Proof.
  (* 실제 동등성 증명 *)
Qed.
```

`v002`의 `equivalent`는 **v001 → v002**를 증명한다. 이후도 바로 앞 후보와
연결하며, 번호는 1부터 연속이어야 한다. 검사기는 각 정리의 정확한 타입을
확인한 다음 전체 연결을 합성한다. 후보 정의와 증명은 별도 파일로 유지한다.

```sh
# 원본 → v001 → v002 → … 전체 동등성 연결만 검사
python3 scripts/check.py properties/<name>

# 원하는 후보까지 연결을 검사하고 해당 후보의 생성기를 도출 (생성기 증명 제외)
python3 scripts/run.py properties/<name> --candidate v002 --derive-only

# 같은 검증 후 생성기를 실행
python3 scripts/run.py properties/<name> --candidate v001 --samples 100 --size 30 --seed 0
```

`run.py`는 선택한 후보까지의 연결을 매번 새로 검사한다. 이후 후보의 미완성
파일은 그 실행을 막지 않는다. 이 브랜치에서는 생성기의 soundness/completeness
증명을 요구하지 않는다. `result.json`에 `generator_proof: "not_checked"`를 기록한다.
`generated`/`failed`는 `Some`/`None`의 수이며, 독립적인 전제 만족 판정 수가 아니다.
샘플 출력에는 `Show Input` 인스턴스가 필요하다. 기본 타입은 QuickChick의
인스턴스를 사용하고, 사용자 타입의 인스턴스는 원본이나 후보에서 제공한다.
`--derive-only`에는 출력 인스턴스가 필요 없다.

현재 `run.py`의 도출 경로는 `Derive ArbitrarySizedSuchThat`이다.
Cedar 비교 실험에는 원본과 모든 후보에 동일한 Testing Theorems 자동 스케줄링
경로를 연결해야 한다. 위의 후보 문법 검사와 원본 다섯 전제의 독립적인 유효성
판정도 아직 실험 도구에 구현하지 않았다. 공식 Cedar 실행 성공과 이 실험 도구의
준비 완료는 구분한다. 비교 대상은 Testing Theorems 하나이며, 앞의 구형 연구
예제들은 환경 호환성 확인용으로 보존한다.

명세·원본·후보의 복사본, 자동 도출한 `Derived.v`, Coq 커널 검사 로그와
`result.json`은 각 property의 `.runs/`에 보관한다. 실행한 경우
`samples.json`도 저장한다. 값은 `Show`로 표시한 문자열이며, 생성 실패는
`null`이다. 생성 실패는 property 반례와 구분한다. 시간은 각 명령별로 기록하며,
샘플 실행 시간에는 출력 문자열을 만드는 시간도 포함된다.
구버전 추출기의 정수 타입 별칭 호환 처리가 필요한 경우 `.ml`과 `.mli`에
동일하게 적용하며, 수정 전 파일과 적용 목록도 결과에 보존한다.

`check.py`의 동등성 증명은 추가 공리 없이 닫혀 있어야 한다.
생성된 정의의 `coqchk` 통과는 생성기 soundness/completeness 증명이 아니다.
추출 코드 치환이나 authored source 안의 실행 명령은 허용하지 않는다.
이 검사는 신뢰할 수 있는 로컬 Coq 개발을 위한 도구이며, 악의적인 Coq 코드의
실행을 격리하는 sandbox는 아니다. 실행 결과는 고정된 Coq/OCaml 추출 런타임을
사용한다. seed는 OCaml driver에서 초기화하며, 같은 실행 파일은 같은 샘플을 재현한다.

각 하위 명령의 시간 제한은 `--timeout 120`으로 조정할 수 있다(초, 기본 120).
검사 중 원본이나 선택한 후보 연결이 바뀌면 실패한다. 이전 로그는 덮어쓰지 않는다.

회귀검사는 다음 명령으로 실행한다.

```sh
python3 -m unittest discover -s scripts/tests -v
```
