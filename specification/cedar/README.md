# Cedar 명세

`Spec.v`는 *Testing Theorems, Fully Automatically* 공식 아티팩트의
`QuickChick/examples/paper-tests/cedar/Cedar.v`에서 논리 정의를 분리한 파일이다.
원본은 Mike Hicks의 Coq formalization을 바탕으로 했다고 명시한다.

- 논문: https://lemonidas.github.io/pdf/TestingTheorems.pdf
- 공식 아티팩트: https://zenodo.org/records/22087774
- DOI: https://doi.org/10.5281/zenodo.22087774
- 바깥 압축 파일: `testing-theorems-final-submission.tar.gz`
- 안쪽 소스 압축 파일: `testing-theorems-final/testing-theorems-artifact-context.tar.gz`
- 안쪽 경로: `testing-theorems-artifact-context/QuickChick/examples/paper-tests/cedar/`

## 포함 범위

표현식 구문, 스키마, 환경, well-formedness, subtype/branch join,
경로 집합과 `HasType` 타이핑 관계를 포함한다. Cedar 전체 언어의 공식 명세가
아니라 논문 아티팩트가 모델링한 부분이다. 평가 의미론이나 Rust 구현은 포함하지 않는다.

원본의 모든 `Inductive` 선언(상호 귀납 선언 포함)을 보존했다.
`WfSchema`의 action ID 중복 제거와 경로 집합 연산도 유지했다.
Coq 8.6.1 호환을 위해 `String.eqb`를 `string_dec` 기반 Boolean 함수로,
QuickChick의 `(x = y)?`를 투명한 구조적 결정 함수로 대체했다.
생성기·축소기·출력기·예제·`Derive Density` 실행은 분리했다.
이 호환 작업 전체에 대한 원본 환경 간 동등성 증명은 수행하지 않았다.

`upstream/Cedar.v.txt`는 원본 바이트를 그대로 보존한다. `.txt` 확장자는
현재 Coq 빌드 및 property 검사기가 원본의 실행 명령을 읽지 않도록 하기 위한 것이다.
QuickChick 소스 트리의 MIT 라이선스는 `upstream/LICENSE`에 보존했다.

원본 SHA-256:

```text
0ff523f080c9e26e15afbc25cc89b519da9c7dd25dfa9a8c2cfb917fc681e911  Cedar.v
```

성질과 생성 전제: [cedar_no_type_error](../../properties/cedar_no_type_error/README.md).
