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

검증된 플랫폼은 Linux x86_64다. Python 3, Git, opam, make, `/usr/bin/gcc`, Perl과
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
현재 QuickChick 도출기가 지원하는 귀납 관계여야 한다. 중간 후보는 생성기를
도출할 수 없는 정의여도 동등성을 증명할 수 있으면 된다.

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

# 원하는 후보까지 연결을 검사하고 해당 후보의 생성기·정확성 증명만 도출
python3 scripts/run.py properties/<name> --candidate v002 --derive-only

# 같은 검증 후 생성기를 실행
python3 scripts/run.py properties/<name> --candidate v001 --samples 100 --size 30 --seed 0
```

`run.py`는 선택한 후보까지의 연결을 매번 새로 검사한다. 이후 후보의 미완성
파일은 그 실행을 막지 않는다. 도출한 생성기에 대해 soundness/completeness를
증명하고, 동등성 연결을 이용해 원본 predicate에 대한 정확성까지 확인한다.
샘플 출력에는 `Show Input` 인스턴스가 필요하다. 기본 타입은 QuickChick의
인스턴스를 사용하고, 사용자 타입의 인스턴스는 원본이나 후보에서 제공한다.
`--derive-only`에는 출력 인스턴스가 필요 없다.

명세·원본·후보의 복사본, 자동 도출한 `Derived.v`, Coq 커널 검사 로그와
`result.json`은 각 property의 `.runs/`에 보관한다. 실행한 경우
`samples.json`도 저장한다. 값은 `Show`로 표시한 문자열이며, 생성 실패는
`null`이다. 생성 실패는 property 반례와 구분한다. 시간은 각 명령별로 기록하며,
샘플 실행 시간에는 출력 문자열을 만드는 시간도 포함된다.
구버전 추출기의 정수 타입 별칭 호환 처리가 필요한 경우 `.ml`과 `.mli`에
동일하게 적용하며, 수정 전 파일과 적용 목록도 결과에 보존한다.

`check.py`의 동등성 증명은 추가 공리 없이 닫혀 있어야 한다. `run.py`의
생성기 정확성에는 QuickChick의 명시된 난수 모델 가정만 허용한다.
추출 코드 치환이나 authored source 안의 실행 명령은 허용하지 않는다.
이 검사는 신뢰할 수 있는 로컬 Coq 개발을 위한 도구이며, 악의적인 Coq 코드의
실행을 격리하는 sandbox는 아니다. 실행 결과는 고정된 Coq/OCaml 추출 런타임을
사용하며, Coq 수준의 가능 출력 집합에 대한 증명이 그 런타임 자체를 증명하지는 않는다.

각 하위 명령의 시간 제한은 `--timeout 120`으로 조정할 수 있다(초, 기본 120).
검사 중 원본이나 선택한 후보 연결이 바뀌면 실패한다. 이전 로그는 덮어쓰지 않는다.

회귀검사는 다음 명령으로 실행한다.

```sh
python3 -m unittest discover -s scripts/tests -v
```
