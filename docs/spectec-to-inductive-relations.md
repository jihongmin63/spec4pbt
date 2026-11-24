# SpecTec의 직접 귀납 관계 번역

번역기는 고정된 SpecTec 프런트엔드의 AL을 typed Action으로 낮춘 뒤,
각 명세 relation과 호출 후속 처리를 별도의 Coq 귀납 관계로 출력한다.
공개 의미는 직접 귀납 관계이며, 공통 `Eval`은 회귀 증명의 비교 기준이다.
생성된 명세와 실행별 증거는 로컬 산출물이다. 입력 revision과 해시,
번역기 구현, 직접 작성한 회귀 및 동치 증명은 Git으로 관리한다.

## 3. 번역 알고리즘

입력은 타입 검사가 끝난 AL 선언과 기존 번역기가 만든 typed Action이다. 출력은 relation마다 별도로 이름 붙인 Rocq `Inductive`와 그 보조 관계다. 이 단계는 생성기나 property 판정기를 만들지 않는다.

| 순서 | 수행할 일 | 산출물과 확인점 |
|---|---|---|
| 1 (§3.1) | AL의 clause와 경로를 실행 순서대로 수집한다. | 각 선언의 입력·출력 타입과 순서가 확정된다. |
| 2 (§3.2) | 호출 지점과 clause 경계를 찾고, 이후에 필요한 지역값을 계산한다. | `R_execute`, `R_after_call_j_at_i`, `R_continue_from_i`의 이름·인자·결과 타입을 본문보다 먼저 확정한다. |
| 3 (§3.3–3.4) | Action을 호출 경계의 순차 구간으로 나누고, 구간 안의 성공·Unmatch·오류 경로를 모두 옮긴다. | 각 구간의 시작 값·상태, 전제, 종료 방식이 정해진다. |
| 4 (§3.5) | 호출 결과와 clause 실패를 보조 관계로 연결한다. | 성공·Unmatch·오류가 각각 올바른 다음 지점으로 간다. |
| 5 (§3.6) | constructor를 만들고 의존 관계에 따라 선언한다. | 생성된 정의가 `Eval` 없이 타입 검사된다. 의미 동치 검증은 §6의 별도 의무다. |

하나의 원래 호출 **지점**에서 생기는 호출 전제를 결과 갈래마다 복사하지 않는 것이 설계 규칙이다. 호출 결과의 성공·Unmatch·오류는 호출 뒤 보조 relation에서 처리한다. 이 구조는 런타임에서 동일한 전제를 다시 실행하라는 뜻이 아니다.

### 3.1 SpecTec을 AL로 정리한다

기존 프런트엔드로 파싱·타입 검사를 수행하고 AL을 얻는다. relation·함수·table·외부 선언의 입력과 출력, clause, 전제와 호출을 식별한다. 번역 대상 선언마다 현재 Action 본문과 대조할 수 있는 순서 있는 clause 목록을 만든다. relation이 호출하는 함수·table·외부 선언도 실행 의미가 필요하다. 별도 실행 관계나 의미가 확인된 primitive를 제공하지 못하면 그 호출을 미지원으로 보고한다. 이후 단계는 AL에 정해진 평가 순서를 보존한다.

rule group에 여러 경로가 있으면 현재 번역기처럼 순서를 유지한다. 각 경로에 속한 공통 전제를 한 번만 실행하도록 임의로 끌어올리지 않는다.

### 3.2 각 relation의 인자 형태를 먼저 정한다

이름을 먼저 실행 위치에 대응시키면 다음과 같다. `R`은 원래 SpecTec relation의 이름이고, `i`는 **clause 번호**, `j`는 **그 clause 안의 호출 지점 번호**다. clause마다 typed Action의 정적 `Invoke` 지점을 순서대로 번호 붙이고, 다음 clause에서 `j = 1`로 다시 시작한다. 이 번호들은 실행 횟수나 재귀 깊이가 아니다. 세 이름은 모두 Coq의 `Prop` 관계다. 값을 계산하는 함수라기보다, 주어진 입력·상태에서 어떤 결과가 **가능한지** 나타내는 판단이다.

| 이름 | 어디서 시작하는 판단인가 | 언제 필요한가 |
|---|---|---|
| `R_execute` | 원래 relation `R`의 첫 clause | `R`을 실행하거나 다른 relation이 `R`을 호출할 때 |
| `R_after_call_j_at_i` | `i`번째 clause의 `j`번째 호출 **결과를 이미 받은 직후** | 그 결과에 따라 남은 명령을 수행하거나 Unmatch·오류를 전파할 때 |
| `R_continue_from_i` | `i`번째 clause의 시작 | 앞 clause가 Unmatch로 끝나 다음 clause를 시도할 때 |

원래 `R(inputs) => outputs`에 대응하는 실행 relation을 다음 형태로 준비한다.

```text
R_execute inputs 시작상태 실행결과

실행결과 = 성공(outputs, 최종상태)
         | Unmatch(최종상태)
         | 오류(오류내용, 최종상태)
```

Unmatch는 호출자와 다음 clause의 동작을 정의하는 데 필요하다. 오류는 이미 일어난 오류를 그대로 전파할 뿐 성공이나 Unmatch 판정에는 쓰이지 않는다. 그래도 기존 `Eval`과 모든 결과가 같음을 확인하고 오류를 관찰하는 property를 지원할 수 있도록 남긴다. 성공한 명세 판단은 이 relation의 성공 결과를 사용한다. 결과와 최종 상태를 별도 인자로 둘 수도 있으며, 여기서는 설명을 위해 묶는다.

따라서 `R_after_call_j_at_i`와 `R_continue_from_i`는 원래 명세의 새 relation이 아니라 `R_execute`를 짧은 실행 구간으로 나누기 위해 번역기가 만드는 내부 보조 관계다. 보조 relation의 인자 형태는 다음과 같다.

```text
R_after_call_j_at_i  지역값 호출결과 실행결과  -- i번째 clause의 j번째 호출 뒤
R_continue_from_i   입력 시작상태 실행결과    -- i번째 clause부터
```

호출 뒤 relation은 **호출을 다시 수행하지 않는다**. 이미 얻은 호출 결과와 최종 상태를 별도 인자로 받아 남은 동작만 표현한다. 지역값에는 이후 구간이 쓰는 값과, Unmatch일 때 다음 clause relation에 넘길 원래 입력이 들어간다. 다음 clause relation도 **앞 clause를 다시 수행하지 않는다**. 원래 입력과 앞 clause가 끝난 상태만 받고 그 clause의 지역 바인딩은 받지 않는다. 어느 보조 relation이든 이후 구간이 쓰지 않는 값은 받지 않는다. `R_execute`는 첫 clause부터의 실행이므로 `R_continue_from_1`을 따로 두지 않는다.

모든 이름과 signature를 먼저 수집한다. 보조 relation의 이름과 signature도 이 단계에서 정한다. 그러면 아직 본문을 번역하지 않은 relation이나 자기 자신도 전제로 참조할 수 있다. 구간마다 이후에 쓰는 지역값을 역방향으로 분석해 `R_after_call_j_at_i`의 인자를 정한다. `R_continue_from_i`에는 원래 입력과 앞 clause의 최종 상태만 넘긴다. 독립 실행의 초기 fresh counter는 0이며, 내부 호출은 호출자의 현재 상태를 이어받는다.

두 clause에 호출이 여러 개 있다면 번호는 다음과 같다. 이는 번호 설명용 의사 문법이다.

```text
R(x)
  clause 1: a <- F(x); b <- G(a); return b
  clause 2: c <- H(x); return c
```

| 실행 지점 | 생성되는 보조 관계 |
|---|---|
| 첫 clause의 `F(x)` 결과를 받은 뒤 | `R_after_call_1_at_1` |
| 첫 clause의 `G(a)` 결과를 받은 뒤 | `R_after_call_2_at_1` |
| 첫 clause가 Unmatch여서 둘째 clause를 시작할 때 | `R_continue_from_2` |
| 둘째 clause의 `H(x)` 결과를 받은 뒤 | `R_after_call_1_at_2` |

`F(x)`가 성공하면 `R_after_call_1_at_1`이 `G(a)`의 전제를 남긴다. 첫 clause의 `F(x)`나 `G(a)`가 Unmatch로 끝나면 `R_continue_from_2`로 이동한다. 둘째 clause의 `H(x)`가 Unmatch이면 다음 clause가 없으므로 전체가 Unmatch로 끝난다. 어느 호출이든 오류는 그 자리에서 전파한다. 둘째 clause의 호출 번호가 다시 1이므로 `_j_at_i`의 두 번호가 모두 필요하다.

### 3.3 본문을 Action으로 정리한다

현재 번역기의 Action 중간 표현을 활용해 호출, 조건, 순차 실행과 clause 선택을 명시한다. 조건·패턴 검사·cast가 일어나는 위치도 유지한다. 특히 구조 불일치로 발생하는 오류를 Unmatch로 바꾸지 않는다. Action은 번역 과정에서 사용하는 표현이며 최종 공개 API를 정하는 것은 아니다.

### 3.4 Action을 호출 지점에서 구간으로 나눈다

구간은 clause의 시작이나 호출 직후에서 시작해 다음 호출이나 종료까지 이어지는 **순차 Action 경로**다. 호출이 없어도 식 계산, builtin, 패턴·구조 검사에서 Unmatch나 오류로 끝날 수 있으므로 구간 전체를 순수식으로 간주하지 않는다. Coq의 값 표현(`Coq_ir.expression`) 중 총함수로 확인된 부분만 constructor의 계산식으로 옮긴다. 번역기는 Action을 앞에서부터 읽으며 다음 정보를 모은다.

```text
현재 지역 변수값 / 현재 상태 / 필요한 전제 / 종료 방식
```

구간은 성공, Unmatch, 오류, 호출 경계 중 하나로 끝난다. Unmatch라면 다음 clause relation으로 이어지고, 마지막 clause면 Miss가 된다. 오류라면 Fault로 끝나며 다음 clause로 가지 않는다. 호출 경계라면 호출 전제와 그 뒤 relation 전제를 남긴다. 조건·패턴 분해와 부분 함수의 `Some`/`None`으로 갈라진 경로에 각각 같은 규칙을 적용한다. 한 경로에서 계산한 지역값은 그 경로의 후속 구간에만 남는다.

기본 동작의 변환 규칙은 다음과 같다.

| 동작 | 구간에 반영하는 내용 |
|---|---|
| `Return v` | 현재 상태에서 성공 `v`로 종료한다. |
| `Fresh` | 현재 counter를 값으로 얻고 counter를 하나 증가시킨다. |
| `Guard` 조건 | 조건식 자체를 먼저 실행한다. 성공해 boolean을 얻으면 참·거짓 전제를 두고, 거짓일 때 Unmatch로 끝난다. 조건식 도중 오류가 나면 그 오류를 전파한다. 어떤 조건이 값의 모양을 묻는지 분석해 패턴으로 바꾸지 않는다. |
| 값의 분해 | 입력이나 호출 결과를 분해하면 각 갈래의 패턴을 결론의 입력이나 호출 결과 자리에 둔다. 계산된 값을 분해하면 갈래마다 `f args = 패턴`을 전제로 둔다. 기본 갈래는 남은 생성자의 패턴으로 나눈다. |
| `Unmatched` | 현재 clause가 현재 상태에서 Unmatch로 끝난다. 다음 clause relation을 그 상태에서 호출하며, 다음 clause가 없으면 Unmatch로 종료한다. |
| `Raise e` | 현재 상태에서 오류 `e`로 종료한다. |
| `Bind a k` | `a`를 먼저 번역한다. 성공값과 최종 상태를 얻은 경로에서만 그 값을 `k`에 대입해 계속한다. `a`가 Unmatch나 오류로 끝난 경로에는 `k`를 붙이지 않는다. `a` 안에 호출이 있을 때만 아래 `Invoke` 경계로 나눈다. |
| `Invoke F(args)` | 전제 `F_execute args 현재상태 r`과 `R_after_call_j_at_i 지역값 r 결과`를 남기고 구간을 끝낸다. 이 호출 전제를 결과의 세 갈래에 다시 쓰지 않는다. |
| 호출 뒤 relation의 세 경우 | 성공 `v`·상태 `t`이면 `v`를 대입하고 `t`에서 다음 구간을 처리한다. Unmatch `t`이면 현재 clause의 Unmatch이므로 다음 clause relation을 `t`에서 호출한다. 오류이면 같은 오류와 상태로 종료한다. |
| `OrElse a b` | `a`가 Unmatch로 끝나는 각 지점에서 `b`의 시작 relation을 그 최종 상태로 호출한다. `a`의 경로와 `b`의 경로를 이어 붙인 constructor를 만들지 않는다. |
| `Negate a` | `a`의 성공을 Unmatch로, 명시적 Unmatch를 unit 성공으로 바꾸며 오류와 최종 상태는 전파한다. `a`의 인자 계산에서 난 오류도 그대로 전파한다. |
| `Choose` | 해당 타입의 선택값을 변수로 두고 성공시킨다. 실제 생성에는 그 타입의 생성 지원이 필요하다. |
| `Primitive_action` | helper가 산출한 Coq Action의 성공·Unmatch·오류와 상태를 각각 이어 준다. 해당 helper의 의미를 직접 귀납 규칙으로 옮기고 `Eval`과 동치를 증명할 수 있을 때만 지원한다. |

`Local`은 같은 구간의 지역 바인딩으로, `Alternatives`는 순서 있는 `OrElse`로, `Match`는 값의 분해로 처리한다. `Traverse`는 원소 하나를 실행한 뒤 남은 목록에 재귀하는 별도 관계를 만든다. 명시적으로 검토한 P4 종료형 builtin과 Wasm의 `WasmScalar.lift`는 helper가 `Return`, `Unmatched`, `Raise` 중 하나라는 등식 전제로 세 결과를 분리한다. P4 `fresh_typeId`는 상태를 소비하는 별도 규칙을 사용한다. 고차 `#apply`는 참조 생성자별 호출 전제를 가진 `R_apply`로 분기하며, 다형성 타입과 `ValueOps` 인자를 관계에 전달한다. 이 계약에 없는 원시 helper는 위치가 있는 진단으로 중단한다.

전제와 인자에 쓰는 함수의 고유 이름 별칭은 의미를 바꾸지 않는 선택적 출력 규칙이다. 생성기 도구의 이름 해석 제약과 실험 근거는 [property 번역 문서](spectec-property-to-precondition.md)에서 다룬다.

호출된 relation의 본문은 펼치지 않는다. 재귀 호출도 relation 전제로 남기므로 번역 과정에서 무한히 전개하지 않는다. 생성기는 관계 의존 그래프의 강연결요소만 mutual `Inductive`로 묶고, 그 블록을 의존 순서대로 작은 Coq 파일에 나눠 출력한다.

### 3.5 순차 의미에 따라 구간을 연결한다

성공하면 다음 명령을 수행하고, clause 전체가 성공하면 그 결과로 종료한다. Unmatch일 때만 다음 clause로 이동한다. 오류는 즉시 전파한다. otherwise에 도달하려면 앞선 일반 clause가 실행 순서대로 모두 Unmatch로 끝나야 한다. 비결정적 호출이 있으면 이는 **하나의 실행 경로에서 앞선 clause가 각각 Unmatch라는 뜻**이다. 같은 입력의 다른 실행 경로에서 앞선 clause가 성공할 수도 있다. 성공 가능성을 전역적으로 검색하는 조건은 아니다.

다음 clause로의 이동은 `R_continue_from_(i+1) 입력 t r`을 전제로 남기는 것으로 표현한다. 한 clause가 Unmatch로 끝나는 방법이 여러 가지여도 각 경우가 같은 다음 clause relation을 부르므로, 실패 방법의 조합만큼 constructor가 늘지 않는다.

다음 clause는 이전 clause의 **최종 fresh 상태**를 이어받지만, 실패한 clause의 지역 바인딩을 이어받지는 않는다. 호출 결과와 호출자의 출력 패턴이 맞지 않아도 피호출자의 다른 clause를 재선택하지 않는다. 구조 오류를 임의로 Unmatch로 바꾸지도 않는다.

성공 증명의 부재, 재귀의 미종료, 생성기의 `None` 또는 크기 한도 소진은 Unmatch가 아니다. 그런 이유로 otherwise를 허용하지 않는다.

### 3.6 구간을 constructor로 출력한다

각 구간에서 모은 조건과 호출은 constructor의 전제가 된다. 결론에는 그 relation의 입력과 종료 결과가 들어간다. 원래 relation과 다음 clause relation의 입력은 원래 입력과 시작 상태이고, 호출 뒤 relation의 입력은 지역값과 호출 결과다. 지역 중간값은 필요한 constructor 변수로 바인딩한다. constructor의 타입이 맞지 않거나 지원하지 않는 Action이 남으면 출력을 성공으로 처리하지 않는다.

원래 clause 하나는 원래 relation 또는 다음 clause relation의 constructor와, 호출마다 생기는 호출 뒤 relation으로 나뉜다. constructor 수는 구간별 경우의 합으로 유지된다. constructor의 나열 순서가 우선순위를 구현하는 것은 아니다. 우선순위는 이미 전제와 상태 전달에 반영되어 있다.

호출 의존성에 순환이 없으면 의존 순서대로 선언한다. 자기 재귀는 같은 relation을 전제로 사용한다. 보조 relation이 원래 relation을 다시 호출하면 원래 relation과 같은 mutual 블록으로 선언한다. 예를 들어 첫 clause의 호출 뒤 relation이 Unmatch에서 둘째 clause relation을 부르고, 둘째 clause가 원래 relation을 재귀 호출하는 경우다. 서로 다른 명세 relation 사이의 상호 재귀도 이름이 분리된 mutual 블록으로 선언한다. 재귀가 얽힌 정의가 Rocq의 귀납 정의 검사에 통과하는지도 확인한다. 재귀 호출이 없는 짧은 보조 relation을 호출자에 합치는 것과 도달 불가능한 경우를 지우는 것은 의미 동치를 확인한 뒤 적용할 최적화다.

구조를 정할 때 비교한 형태는 다음과 같다. 소형 예제의 의미 동치 근거는 §6에 있다.

| 형태 | 장점 | 한계 |
|---|---|---|
| 실행 경로 전체를 constructor로 펼침 | 원래 clause와 constructor의 대응이 단순하다. | 호출 결과마다 호출 전제가 복사되고 clause 실패 방법의 조합만큼 constructor가 늘어난다. |
| 호출 뒤·다음 clause를 별도 보조 relation으로 둠 (채택) | 호출 전제를 결과 갈래마다 복사하지 않고 후속 실행을 분리한다. | 보조 relation이 원래 relation을 다시 호출하면 mutual 블록이 된다. |
| 보조 relation 대신 같은 relation의 실행 지점 인덱스를 둠 | mutual 블록을 줄일 수 있다. | 지점 자료형이 relation마다 필요하고 원래 relation의 모양이 흐려진다. |

### 5.2 오류를 분류할 때의 기준

원본의 예외 이름보다 **해당 호출 경계에서 관찰되는 결과**를 먼저 확인한다.

| 원본에서 일어난 일 | AL 내부에서의 의미 | 번역 시 지켜야 할 구분 |
|---|---|---|
| `back_err` / `Err` | 현재 실행을 중단한다. 다음 clause로 가지 않는다. | `Error`; `Unmatch`로 바꾸지 않는다. |
| 거짓 `IfPr`, 모든 clause의 불일치, `back_unmatch` | `Unmatch` | 다음 clause 및 otherwise를 허용한다. 부정에서는 성공으로 바뀐다. |
| builtin이 `BuiltinError`를 던짐 | `invoke_builtin_func`가 잡아 `Unmatch`로 바꾼다. | 이름에 Error가 있어도 이 경계의 결과는 `Unmatch`다. |
| 외부 구현이 `Run.Fail (Run.Unmatch ...)` 반환 | `Unmatch` | 외부 실패 계약을 구현하는 경우 동일하게 전달한다. |
| 외부 구현의 `Run.Abort` / `ExternError (Abort ...)` | backtracking을 막는 외부 중단 | 외부 실패 계약을 구현하는 경우 `Error`로 전달한다. |
| 잡히지 않은 OCaml 예외 | 호스트 실행 중단 | 현재 Coq는 일부를 `HostConversion` 등으로 정규화한다. 예외별 대응을 기록해야 한다. |
| Wasm `eval_numresult`가 수치 예외를 잡음 | 정상적인 `NumTrap` 값 반환 | `Success NumTrap`; 실행기의 `Error` 또는 `Unmatch`가 아니다. |

AL의 공개 `eval_func`/`eval_rel` 진입점은 내부 `Err`와 `Unmatch`를 모두 `Run.Fail (Run.Unmatch ...)`로 내보낸다. 따라서 **최상위 실패 출력만 비교하면 otherwise를 차단하는 내부 오류를 놓친다.** clause 내부에 실패를 놓고 다음 분기로 가는지까지 검사해야 한다.

현재 `ErrorKind = ALAbort | ExternalAbort | HostConversion | HostInvalidArgument | StructureError | NumericTrap`은 Coq의 분류이며, 원본 예외와 일대일인 목록이 아니다. 예를 들어 원본의 0 나눗셈과 `PowOp`는 모두 `Assert_failure`로 끝나지만 현재 번역은 각각 `HostConversion`, `ALAbort`를 사용한다. 이 분류를 곧 원본 예외 종류의 보존이라고 부르지 않는다. slice 경로의 잡히지 않은 `Invalid_argument message`는 `Error (HostInvalidArgument, message)`로 구분한다.

### 5.3 AL 식·본문의 오류 목록

아래의 “처리 있음”은 해당 Coq 분기가 있다는 뜻이다. 전체 입력에 대한 native 동치가 증명되었다는 뜻은 아니다. 앞서 실행되는 AL guard가 Unmatch를 만들면 뒤의 부분식에는 도달하지 않는다.

| ID | 발생 조건과 원본 경로 | 현재 Action/Eval 처리 | 남은 확인 |
|---|---|---|---|
| A1 | nat/int 나눗셈·나머지의 분모 0. `Num.bin`의 마지막 assertion | `divide_*`/`remainder_* = None` → `HostConversion("partial expression failed")` | 나눗셈 수정 반영됨. 네 연산 각각의 AL 경계·상태 회귀를 구분한다. |
| A2 | `PowOp`. 고정 원본 `Num.bin`에 성공 구현 없음 | 피연산자 평가 후 `ALAbort` | 정상 거듭제곱으로 바꾸지 않는다. P4 builtin `pow2`와 별개다. |
| A3 | list/text 인덱스 및 slice 범위 초과. 접근·갱신 경로 모두 포함 | 부분 helper의 `None` → `ALAbort` | 처리 있음. frontend가 삽입한 guard의 Unmatch와 구분한다. slice 합 overflow는 A4. |
| A4 | 인덱스의 `Bigint.to_int_exn` 범위 초과; 변환 후 `start + count`의 OCaml int overflow | 각 인자의 `2^62 - 1` 초과는 `HostConversion`; 합 overflow 시 list 읽기는 빈 목록, 길이가 맞는 list 갱신은 원래 목록, text 읽기·길이가 맞는 text 갱신은 `HostInvalidArgument` | 합 overflow 입력도 처리한다. 갱신의 대체값 길이 오류는 native 순서대로 `ALAbort`이며, 중첩 경로의 부모 slice 접근은 먼저 실행한다. |
| A5 | text 한 글자 갱신에 길이 ≠ 1; list/text slice 갱신에 대체값 길이 ≠ count | `splice_* = None` → `ALAbort` | 처리 있음. `rejects_text_resize`, `rejects_list_resize` 회귀 존재. |
| A6 | 실행 가능한 cast의 변환 실패. 예: 음수 int → nat | cast helper `None` → `ALAbort` | 처리 있음. 원본 assertion·선행 subtype guard의 도달 가능성을 구분한다. `SubE`는 실패 시 bool `false`를 반환하는 검사다. |
| A7 | 배정·호출 결과 분해의 list 길이, option 모양, constructor 불일치; 인자/결과 개수 불일치 | 동적 모양 불일치 → `StructureError`; 일부 arity는 번역 시 거부하거나 Coq 타입으로 배제 | typed frontend가 보장하는 조건과 runtime에서 가능한 조건을 구분한다. 원본의 `Err`, assertion, `List.hd/tl` 실패를 하나의 예외 종류로 보지 않는다. |
| A8 | 식·premise 반복의 list 길이 불일치, option의 Some/None 혼합 | `StructureError`; `Traverse` 내부의 Unmatch/Error도 전파 | 처리 있음. 첫 실패 지점, 앞선 Fresh, 후속 원소 미실행 회귀가 필요하다. |
| A9 | 정의되지 않은 값·타입·함수·relation, 중복 지역 타입/함수, 잘못된 고차 인자 | 많은 경우 번역 진단 또는 typed 참조로 배제 | 원본 `Ctx`의 `Err`를 모두 runtime Error로 구현한 상태가 아니다. 닫힌 well-formed AL이라는 입력 계약과 배제 근거가 필요하다. |
| A10 | runtime 타입 guard 실패, `Value.Get.*`의 잘못된 값 종류, 없는 record field, 잘못된 tuple/type 인자, 타입 확장·고차 치환 오류 | typed Coq 값이 다수를 배제; 남은 부분 cast·구조 검사만 명시적 오류 | 원본의 `RuntimeError`, `Not_found`, `Invalid_argument`, assertion 및 mixfix arity 오류가 관련된다. 원시 native 값 전체를 받는 인터페이스의 동치는 아직 주장하지 않는다. |

대표 근거는 원본 수치 연산 (고정 프런트엔드 소스), AL context (고정 프런트엔드 소스), 값 분해 (고정 프런트엔드 소스), 현재 [식 회귀](../translator/tests/expressions/OperationsChecks.v)와 [순차 실행 회귀](../translator/tests/lowering/SequentialChecks.v)다. 예를 들어 `missing_list_index` 회귀의 결과는 선행 guard 때문에 `Unmatch`다. 반면 부분 helper 자체가 범위를 거부하면 `ALAbort`다.

### 5.4 builtin·외부 경계의 실패 목록

| ID | 발생 조건 | 현재 처리와 감사 판단 |
|---|---|---|
| B1 | P4 `max_nat`/`min_nat`의 빈 입력, signed bits의 빈 입력, width/shift > 2048 | native `BuiltinError` → AL `Unmatch`; Coq도 `Unmatched`. 처리 있음. |
| B2 | P4 `text_to_int` 형식 오류, `split_text` 구분자 길이 ≠ 1, 없는 prefix/suffix 제거 | native 호스트 예외; Coq `HostConversion`. 처리 있음. |
| B3 | P4 `partition_`의 호스트 int 범위 초과, `adds_map`의 key/value 길이 불일치, `bitacc`/`bitacc_replace`의 음수 또는 비호스트 low index, `print_` unparse 실패 | Coq `HostConversion`. 처리 있음. `int_to_bits_*`의 음수 폭도 helper에서는 오류지만 현재 profile 인자는 nat여서 adapter로는 도달하지 않는다. |
| B4 | native `transpose_`의 비직사각 행렬; 잘못된 set/map/pair 구조; builtin arity 오류·미등록 이름 | native `BuiltinError`는 AL `Unmatch`; 다른 구조 예외는 별도. `transpose_` helper와 native 회귀는 있지만 현재 profile에는 선언/adapter가 없다. 나머지는 typed 입력·signature 검사로 배제되는지 확인한다. |
| B5 | Wasm 정수 divide/rem의 0, signed min/-1 나눗셈 overflow, 비포화 float→int의 NaN/범위 초과 | 내부 helper는 `NumericTrap`. **명세 builtin `eval_binop`/`eval_cvtop`은 이를 `Success NumTrap`으로 바꾼다.** 이 경로는 처리 있음. min/-1의 remainder와 포화 변환은 성공이다. |
| B6 | Wasm 수치/float/v128 표현 범위, byte > 255, 호스트 int 변환, memory metadata 범위 | helper의 `HostConversion`을 `eval_*` adapter는 `Unmatch`로 올린다. 직접 호출 builtin의 호스트 변환 오류는 `Error`로 남는다. |
| B7 | Wasm opcode·피연산자 tag·SIMD shape/shuffle·packed memory 조합 불일치 | `eval_*` adapter의 `StructureError`는 원본 catch 경계에 따라 `Unmatch`로 올린다. |
| B8 | Wasm `slice_bytes`/`replace_bytes` 범위 초과·합 overflow, SIMD lane 추출 범위 초과, 짧은 v128 load | 두 byte helper의 명시적 범위 오류와 `eval_*`의 catch 오류는 `Unmatch`다. 직접 호출 byte helper의 호스트 변환 오류와 합 overflow에 따른 `HostInvalidArgument`는 `Error`로 남는다. |
| B9 | extern의 Unmatch·Abort, 미구현 extern, boot/sim의 파싱·변환·호출 실패 및 외부 상태 | 현재 `ExternRelD`/`ExternDecD`는 `Choose`로 성공값만 비결정적으로 선택한다. 실제 외부 구현의 실패·상태는 **모델링되지 않았다**. 이는 비결정성을 없앨 이유가 아니라, native 전체와의 동치 범위를 제한하는 계약이다. |

Wasm의 byte alias는 nat다. `i32_of_bytes`/`i64_of_bytes`는 native에서 임의의 nat 원소를 받아 계산하고, `repeat_byte`도 입력 byte를 그대로 보존한다. 모든 byte 관련 helper에 동일한 범위 오류를 추가하면 원본과 달라진다. 마찬가지로 부동소수점 연산의 NaN/무한대 결과 자체나 명세 안의 trap·throw·P4 오류 값은 실행기 `Error`와 별개다.

### 5.5 확인한 차이와 모델의 경계

**Wasm wrapper의 catch 경계를 반영했다.** donor `nats.ml`의 `trap_as_unmatch`는 예외를 `Builtin.Error.error`로 바꾸고, AL `invoke_builtin_func`는 이를 `Unmatch`로 바꾼다. 모든 선언된 `eval_*` adapter에서 helper의 실패를 `Unmatch`로 올리고, `slice_bytes`·`replace_bytes`에서는 명시적 범위 오류만 `Unmatch`로 올린다. 직접 호출 helper의 호스트 정수 변환 오류는 `Error`로 남는다. `eval_binop`/`eval_cvtop`의 수치 trap은 변환 전에 이미 `Success NumTrap`이므로 유지한다. byte helper의 `offset + count`와 `offset + replacement_length`가 overflow하면 원본의 명시적 범위 검사를 통과한 뒤 `Value_array.sub` 또는 `Value_array.replace_slice`가 `Invalid_argument`를 던진다. 이 결과를 동일 메시지의 `HostInvalidArgument`로 보존하고, fallback·부정에서도 전파한다. `failure_policy`도 이 구분을 기록한다.

**slice 합의 호스트 overflow는 경로별로 처리한다.** pinned 64-bit OCaml에서 `start = 2^62 - 1`, `count = 1`은 각각 int 변환에 성공하지만 합은 음수가 된다. list 읽기는 빈 목록, 길이가 맞는 list 갱신은 원래 목록을 반환한다. text 읽기는 `HostInvalidArgument("String.sub / Bytes.sub")`이고, text 갱신은 대체값 길이를 먼저 검사한다. 길이가 다르면 `ALAbort`, 같으면 동일 호스트 예외다. lowering은 마지막 갱신 위치의 slice를 먼저 읽지 않으며, 중첩 경로에 필요한 부모 slice는 원본대로 읽는다. **합이 호스트 범위 안이어야 한다는 비교 전제는 삭제했다.** 각 인자 자체의 변환 실패도 기존 `HostConversion` 경로로 처리한다.

검증은 [고정 native 실행기·byte 함수의 경계 검사](../translator/tests/expressions/native_slices.py), [63비트 signed 합과 overflow 판정의 일반 Coq 정리](../translator/tests/runtime/ValueOperations.v), [생성된 직접 관계의 모든 overflow 인자에 대한 명제](../translator/tests/expressions/OperationsChecks.v), [byte helper의 일반 명제](../translator/tests/builtins/wasm/WasmBuiltins.v), [실제 adapter의 fallback·부정 검사](../translator/tests/builtins/wasm/wrapper_main.ml)에 포함한다. native 검사는 donor patch의 hash를 확인하고 byte 함수 본문과 `Value_array`를 그대로 실행한다. 유한 native 회귀와 Coq의 일반 경계 명제는 구분하며, 이를 번역기 전체에 대한 일반 의미 보존 정리로 확대하지 않는다. 이전 native 재현 로그 (고정 프런트엔드 소스)도 보존한다.

**원본 오류의 상세 정보는 이미 일부 소실된다.** 여러 부분식 실패가 `"partial expression failed"`로 합쳐지고, 원본 source region·중첩 failtrace는 `ExecutionError`에 없다. `Unmatch`에도 trace가 없다. 따라서 이 문서의 “오류 내용 보존”은 우선 **현재 Action이 가진 kind/detail을 새 귀납 관계에 보존**한다는 뜻이다. native 동치에서는 오류 대응 함수와 진단 정보의 보존 범위를 별도로 정의해야 한다.

다음 항목을 빠진 `Raise`와 혼동하지 않는다.

| 항목 | 현재 범위와 필요한 명시 |
|---|---|
| 결정성 검사 모드의 여러 성공 clause | native `det=true`는 `Nondet_det`를 `Err`로 바꾼다. 현재 설계는 순서 있는 clause 선택과 `Choose`의 비결정성을 유지하며 이 검사 모드를 재현하지 않는다. 성공 뒤 다른 clause를 추가 실행하는 절차도 도입하지 않는다. |
| frontend 파싱·elaboration·AL 생성·profile/signature 오류 | 실행할 Action을 만들기 전의 진단이다. `Error` constructor가 필요한 runtime 분기와 별도로 번역을 중단한다. |
| 프로그램 파싱·STF·boot/sim·I/O 실패 | typed 명세 relation의 외부 경계다. 외부 구현을 포함할 때 별도 계약이 필요하다. SL/PL 실행기도 이번 AL 동치 대상이 아니다. |
| 메모리 고갈·stack overflow·timeout·발산·탐색 fuel 소진 | 현재 `Outcome`이 모델링하지 않는다. `Unmatch`나 “성공 없음”으로 바꾸지 않는다. 자원 제한 실행에서는 별도의 미판정/실행 중단으로 기록한다. |
| native Fresh counter의 machine-int wraparound | 현재 상태는 무한한 Coq nat다. 원본 전체 상태와의 동치에는 wraparound 전 범위 또는 호스트 상태 모델이 필요하다. 정상적인 Fresh 전파 규칙 자체와는 별개다. |

## 6. 의미 보존과 확인한 근거

목표 동치는 모든 입력·초기 상태·실행 결과·최종 상태에 대해 기존 `Eval`과 새 `R_execute`가 양방향으로 일치하는 것이다. 가능한 비결정적 실행을 모두 비교한다. 성공 출력만 맞추거나 유한 샘플을 비교하는 것으로 대체하지 않는다.

이는 `Eval → R_execute`의 목표다. native SpecTec까지 포함한 의미 보존을 주장하려면 아래 오류 대응, typed 입력 영역, 실행 모드, extern 및 호스트 정수·상태의 범위를 먼저 고정해야 한다. 아래의 text·갱신·byte 경로는 호스트 합 overflow도 처리한다. 새 귀납 관계와 현재 Eval의 동치 증명을 native SpecTec 전체의 일반 의미 보존 증명과 구별한다.

`Bind`는 성공에서만 후속 Action을 수행하고 Unmatch·오류를 전파한다. `OrElse`는 왼쪽이 Unmatch일 때만 오른쪽을 수행한다. `Negate`는 성공과 Unmatch만 뒤집고 오류를 보존한다. `Fresh`는 모든 결과의 최종 상태에 반영한다. 호출 전제와 구간 보조 relation의 동치만으로는 부족하며, 호출 없는 오류와 builtin·반복 경로도 각각 동치로 확인해야 한다.

검증 순서는 (1) 출력된 귀납 정의의 Coq 타입 검사, (2) 각 Action 분기와 대표 명세의 양방향 동치 증명, (3) 전체 명세 회귀다. 생성된 관계 정의에는 `Eval` 전제가 없고, 작성한 증명에는 새 공리나 `Admitted`가 없다. [기본 분기 증명](../translator/tests/inductive/InductiveChecks.v), [Fresh 증명](../translator/tests/inductive/FreshChecks.v), [반복 증명](../translator/tests/inductive/TraverseChecks.v), [builtin 증명](../translator/tests/inductive/BuiltinChecks.v), [다형성·고차 호출 증명](../translator/tests/inductive/HigherOrderChecks.v)이 Coq 커널 검사를 통과했다. [반복 첫 실패 증명](../translator/tests/inductive/TraverseFailureChecks.v)은 상태를 바꾸는 호출을 포함한 반복의 모든 입력·결과·최종 상태에 대한 양방향 동치를 증명하고, 두 번째 원소의 Unmatch에서 앞선 Fresh 두 번의 상태를 보존한 실행을 확인한다. `python3 -B translator/tests/check.py --suite all`은 기본 출력으로 P4·Wasm의 직접 관계 전체를 생성·Coq 검사한다. 실행별 manifest와 로그는 각 작업 트리의 무시 대상 `_opam-testing-theorems/`에 보존한다. 전체 번역기에 대한 일반 의미 보존 정리는 아직 없다. `R_apply`의 동치 증명은 현재 단일 참조의 순수 함수 사례이며, 전체 P4·Wasm의 다양한 참조와 실패하는 피호출자에 대한 일반 증명은 아니다. 호출 없는 나눗셈 오류는 기본 분기 증명에서 양방향 동치를 확인했다.
