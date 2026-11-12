# 생성기 언어 실험

## 목적과 이번 범위

조건을 만족하는 입력을 빠르고 다양하게 생성하면서, 이후 생성 결과 집합과 실제 실행의 연결을 검증할 수 있는 작성 방식을 찾는다.
현재 단계는 실행 비교와 번역 도구 적용이다. Soundness·completeness·번역 보존 증명은 아직 하지 않는다.
필수 조건은 ITP 안에서 생성 결과 집합을 정확히 표현하고, 그 집합을 실제 실행 코드와 연결하는 것이다.
고정된 크기·깊이·실행 한도의 completeness와 설정 전체의 completeness를 구분한다.
생성 가능성에 관한 증명과 실행비용·분포의 다양성은 별도로 평가한다.
Palamedes 보강과 Basalt도 비교했으며, 현재 선택은 Rust/Haskell 번역 실험 진행이다. 최종 전환은 아직 결정하지 않았다.

## 실행 비교

정수·불리언·변수·let·if를 갖는 작은 언어에서 타입이 맞고 자유변수가 없는 정확히 N노드의 식을 생성했다.
네 agent는 서로의 구현을 보지 않았다. 크기 16/64/256/1024, 시작 seed 3종, 각 3회로 총 144회 측정했다.

| 구현 | 256노드 식/초 | 최대 RSS 중앙값 |
| --- | ---: | ---: |
| Palamedes | 1,847 | 64.1 MiB |
| Basalt | 22,287 | 65.4 MiB |
| Rust | 47,369 | 3.3 MiB |
| Haskell | 45,119 | 10.5 MiB |

시간은 생성과 전체 AST 순회를 포함하고 JSON 출력은 제외한다. 각 3,000개 표본의 타입·범위·크기·체크섬 검사를 통과했다.
Rust/Haskell의 해당 표본 AST는 동일했다. 64노드 표본은 네 구현 모두 1,000개의 서로 다른 구조를 생성했다.
난수·분포·컴파일러가 다르므로 언어 자체의 순위나 completeness를 뜻하지 않는다.
Lean 메모리의 대부분은 1노드 실행에도 나타나는 기본 프로세스 비용이다.
Basalt는 Lean4.34.1에서 증명 구문 세 곳만 호환 수정했고, Palamedes는 Lean4.31.0과 표준 실행기를 썼다.

원자료·소스·측정 스크립트는 원래 작업 트리의 `build/scratch/GeneratorComparison20261111/`에 보존되어 있다.

## 작성 시간

환경 준비 이후 agent 세션 시작부터 관측한 경과 시간이다. 순수 작성 시간이나 CPU 시간이 아니다.

| 구현 | 첫 네이티브 빌드 성공 | 자체 검사 통과 | 작업 종료 |
| --- | ---: | ---: | ---: |
| Haskell | 2분 57초 | 3분 4초 | 4분 26초 |
| Rust | 4분 23초 | 4분 33초 | 6분 6초 |
| Basalt | 3분 23초 | 5분 51초 | 8분 16초 |
| Palamedes | 9분 3초 | 9분 20초 | 9분 47초 |

Haskell이 가장 빨리 끝났지만, Basalt의 첫 빌드는 Rust보다 빨랐다.
Basalt는 2,560개 표본·1,028회 비교를 검사했고 불필요한 재빌드를 약 2분 기다렸다.
다른 검사량은 Palamedes 192개, Rust 896개, Haskell 928개였다.
Palamedes에는 약 2분 34초의 빌드 환경 진단과 작은 소스 오류 두 건의 수정이 포함된다.
따라서 Rust/Haskell이 모두 Basalt보다 훨씬 작성하기 쉽다는 결론은 지지되지 않는다.
기록 근거는 원자료 디렉터리의 `authoring-audit.json`이며, 설치·스케줄링 대기는 위 구간에서 제외했다.

## 번역 적용

기준 커밋: `P4-spectec-based`의 `4e5947216e1b19e9f756752759e699c9e012988b`.
아래 worktree 경로는 원래 저장소 `/home/min/spec4pbt` 기준이다.

| 브랜치 | 경로 | 목표 |
| --- | --- | --- |
| `generator-in-rust` | `build/worktrees/generator-in-rust` | 기존 Rust 생성기 → Charon → Aeneas → Lean |
| `generator-in-haskell` | `build/worktrees/generator-in-haskell` | 기존 Haskell 생성기 → hs-to-rocq → Rocq/Coq |

공식 도구: [Aeneas](https://github.com/AeneasVerif/aeneas), [hs-to-rocq](https://github.com/plclub/hs-to-rocq).
Rust는 Aeneas `nightly-2026.10.12-d119a47`, Rust `nightly-2026-09-17`, Lean `4.31.0`을 사용한다.
Haskell은 hs-to-rocq `5e6a7bdd`, GHC `9.10.3`, Rocq `9.0.0`을 사용한다.
정확한 버전·다운로드 해시는 각 `experiments/generator-*/toolchain.toml`에 고정했다.
Rust는 iterator 두 부분을 반복문으로 바꾸어 실제 Lean 소스 생성에 성공했다.
Lean 기본 타입과 이름이 충돌한 타입 생성자 `Bool`은 번역 대상에서 `Boolean`으로 바꾼다.
Haskell은 재귀에 fuel을 추가하고, `Word64` 덧셈·곱셈을 구체적인 modulo-2^64 연산으로 연결했다.
CLI·JSON 출력은 번역 밖에 두었다. 원본은 `original/`에 보존하고, 수정본과 원본의 192개 AST가 일치함을 확인했다.
실제 번역 결과가 Lean/Rocq에서 컴파일되었다. Rust→Lean은 193개 AST·최종 RNG 상태가 원본과 일치했다.
Haskell→Rocq는 64개 AST·digest와 30개 RNG 연산(총 158개 평가)이 일치했고, 검사한 6개 정의는 추가 공리가 없었다.
Haskell의 `replicate`는 upstream Rocq 정의가 실행되지 않아 별도 `SequenceBridge`의 `List.repeat`/`Z.to_nat`에 연결했다.
이 라이브러리 대응과 Word64 모델의 의미 보존은 아직 증명하지 않았다. 재현 명령은 각 번역 스크립트와 검사 모듈에 있다.
실제 Wasm `Module_ok` case study의 공통 명세·검사기·인터페이스는 [실험 안내](../experiments/wasm/README.md)를 따른다.
독립 실험으로 적용하며 기존 P4 인증기·명세·루트 Lean 의존성은 변경하지 않는다.
설치물·빌드 결과는 무시되는 `build/`에 두고, 소스·재현 명령은 각 브랜치의 변경 사항으로 남긴다. 커밋은 만들지 않는다.

## Wasm case study 결과와 다음 결정

GPT-6 Sol(xhigh) 두 에이전트가 별도 tmux/worktree에서 독립적으로 작성했다. 무거운 빌드와 ITP 실행은 공통 잠금으로 직렬화했다.
동일한 고정 Wasm 명세의 실제 `Module_ok`를 native SpecTec AL로 실행했다. 두 경로 모두 후보 거부 없이 i32 함수·지역변수·산술·block·if·call·고유 export를 구성하고, 실제 생성기 본문을 ITP로 번역·컴파일했다.

| 확인 항목 | Rust → Lean | Haskell → Rocq |
| --- | --- | --- |
| 함수/구성 깊이 상한 | 4개 / 5 | 6개 / 4 |
| 함수 매개변수 | 함수 위치에 따라 0·1·2개 고정 | 함수별 0·1·2개 선택 |
| 정수 상수 범위 | 전체 u32 | 0..255 |
| `Module_ok` 표본 통과 | 84/84 | 140/140 |
| 서로 다른 전체 모듈 | 59 | 70 |
| 네이티브·번역 결과 전체 비교 | 84/84 | 28/28 |
| 오류 변형 거부 | 7/7 | 7/7 |
| 에이전트 전체 경과 시간 | 22분 36초 | 18분 33초 |

경과 시간에는 번역 오류 수정·검사·공통 잠금 대기가 포함된다. 범위·분포·검사량이 달라 작성 편의성이나 성능의 순위를 뜻하지 않는다.
크기 상한 포화와 일부 seed 중복으로 표본이 반복된다. 실행 검사이며, 보편적인 soundness·completeness·번역 의미 보존 증명은 아직 없다.
메모리·테이블·전역변수·import·start·참조 타입 등은 생성 범위에서 제외했다. 형식적인 `module_ok` 정리는 아직 두 생성기와 연결하지 않았다.
상세 구현·재현 명령·증거는 [이 브랜치의 case study](wasm-generator-case-study.md)에 있다.

발견한 핵심 제약은 다음과 같다.

- Rust: 상호 재귀 안의 호출 인자 반복문은 생성된 Lean의 단조성 검사에 실패했다. 실제 Rust를 0·1·2개 인자 분기로 바꾸어 해결했다. `Result`/`partial_fixpoint`의 성공·종료는 별도로 증명해야 한다.
- Haskell: 구조적 fuel로 재귀를 번역했다. 정수 `Int→Z`, `Word64→N`과 wrapping 연산, 실행 가능한 `replicate` 대응은 별도 의미 보존 과제다. 공리가 없다는 검사만으로 원본 Haskell과 동치가 되지는 않는다.
- 공통: 생성기 내부의 제한된 AST를 전체 명세 AST로 옮기는 JSON/embedding 연결을 증명해야 한다. 현재 serializer와 native AL 검사기는 검증 실험의 신뢰 경계다.

다음 연구는 **Rust 경로에서 현재 부분집합의 soundness부터 연결**하는 것을 권한다. 기존 SpecTec→Lean 경로를 재사용하고, 명령 생성의 스택/지역변수/호출 인덱스 불변식 → 함수 → 모듈 순으로 진행한다. Haskell은 비교 경로로 유지하되 같은 pinned Wasm 명세를 Rocq에 연결하는 방법과 비용을 먼저 정한다.

착수 전에 결정할 것은 (1) 정확한 대상 부분집합과 크기/깊이 설정, (2) 실제 PBT가 원본 코드와 번역 코드 중 무엇을 실행할지, (3) completeness를 실제 유한 seed 공간과 선택 tape 중 무엇에 대해 말할지다. 현재 실행 코드의 support는 허용 설정·seed에서 번역된 생성기가 성공하여 반환하는 출력으로 정의할 수 있다. 독립적으로 정한 목표 영역과의 일치를 증명해야 하며, support 자체를 목표 영역으로 삼는 것은 의미 있는 coverage 증명이 아니다. 선택 tape를 도입한다면 실제 생성기에도 그 입력을 연결해야 한다.
