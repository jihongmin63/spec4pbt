# Cedar: prop_no_type_error

공식 아티팩트의 `CedarWellTypedTermGenerator.v`에 있는
`prop_no_type_error`(304–313행)를 옮겼다.
[명세와 출처](../../specification/cedar/README.md)를 함께 참고한다.

`Original.v`는 다음을 분리한다.

- `Input`: 원본의 일곱 변수 `ets`, `acts`, `rs`, `e`, `es`, `ty`, `expr`.
  `expr`는 표현식 하나가 아니라 `CedarExpr * PathSet`이다.
- `predicate`: 생성에 필요한 아래 다섯 전제의 conjunction.
- `conclusion`: 해당 입력의 외부 검사 결과가 `true`라는 조건.
- `property`: 전제를 만족하는 모든 입력이 결론을 만족한다는 명제.
- `prop_no_type_error`: 원본의 연속된 implication 형태를 유지한 명제.
- `property_matches_artifact`: 두 명제 표현의 동등성만 증명한 보조정리.

생성 전제는 다음과 같다.

1. `EntityType1`, `EntityType2`에 대한 스키마의 `WfSchema`.
2. action 스키마로부터 요청 타입 목록을 만드는 `ActionSchemaToRequestTypes`.
3. 그 목록으로부터 비어 있지 않은 환경 목록 `e :: es`를 만드는 `SchemaToEnvironments`.
4. 같은 두 entity 이름에 대한 결과 타입의 `WfCedarType`.
5. 빈 입력 경로 집합에서의 `HasType (somepaths []) e expr ty`.

원본의 검사기는 스키마, principal(`e1`), action, resource(`e2`),
`fst expr`를 문자열로 직렬화하고 OCaml을 통해 Rust 서버를 호출한다.
`foo.ml`은 타입 오류뿐 아니라 `Err: `, `Parse error: `, `Context error: `,
빈 응답과 통신 예외도 실패로 처리한다. 후속 adapter는 이 동작을 재현해야 한다.
현재 `Checker`는 명시적인 함수 인자이며 구현에 연결되지 않았다.

## 현재 상태

명세와 성질은 처음 Coq 8.6.1에서 검사했으며, 현재 Coq 8.20.0에서도 컴파일했다.
`property_matches_artifact`는 추가 공리 없이 닫혀 있다.
이는 Cedar 구현의 정확성이나 생성기의 soundness/completeness 증명이 아니다.
공식 아티팩트 환경에서 원본 `Cedar.v`와 `CedarWellTypedTermGenerator.v`를
그대로 실행했다. `quickchick 2.`로 도출한 생성기와 실제 Cedar 4.8.2 서버의
차등 검사는 10,000회 통과, 2,386회 discard였다. 실행 시간은 4.677초다.
로그: `_opam-testing-theorems/checks/cedar.uJ7gh2PI/` (저장소 루트 기준).
이는 원본 아티팩트 실행이며, 이 폴더의 `Checker` adapter 연결이나 agent 후보
실험을 완료한 것은 아니다. 구형 도출 방식의 Cedar 제한은 [루트 README](../../README.md)를 참고한다.

원본은 `quickchick 2.` 후 `Admitted.`로 끝난다. 그 선언과 외부 호출용
`Axiom`/추출 치환은 실행 가능한 `Original.v`에 가져오지 않았다.
원본 전체와 검사기의 OCaml 소스는 `upstream/*.txt`에 그대로 보존한다.
소스 트리의 MIT 라이선스도 함께 보존했다.

원본 SHA-256:

```text
3063d50f086691301cc3f1c0a81e9776c0f0159cfde685cf71979785198529cd  CedarWellTypedTermGenerator.v
cfdaeab770dae0cf215b93102e39f1cd75b8d7b272c5080c16abed3a3bf66e70  ocaml/foo.ml
```

로컬 환경 설치 후 작성 파일만 확인하려면 다음과 같이 실행한다.

```sh
bash environment/env.sh coqc -q -R specification Specification specification/cedar/Spec.v
bash environment/env.sh coqc -q -R specification Specification -R properties/cedar_no_type_error Property properties/cedar_no_type_error/Original.v
bash environment/env.sh coqchk -silent -R specification Specification -R properties/cedar_no_type_error Property Specification.cedar.Spec Property.Original
```

최초 검증은 기존 `predicate-reformulation` worktree의 설치된 Coq 바이너리를
읽기 전용으로 사용했고, 소스 복사본과 로그는 이 property의 `.runs/import-check.*`에 보관했다.
기존 worktree나 환경 설정은 변경하지 않았다.
Cedar 자동 스케줄링 실험의 실행 방법과 측정 계약은
[실험 도구 문서](../../scripts/cedar/README.md)를 참고한다. 각 독립 run의 후보
연결은 `experiments/<experiment-id>/run-NNN/`에, 원시 증거는 이 property의
`.runs/<experiment-id>/`에 보관한다. 실제 완료 범위는 해당 실행 결과로 확인한다.
