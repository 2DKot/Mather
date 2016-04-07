/*
***ПЛАН***
+ Разбор на токены
+ Обратная польская запись
+ Вычислитель обратной польской записи
+ переменные. пока задаются вручную в фактах
- парсинг одной функции, let x = expression
- функция - это набор строк (lines)
- программа - это набор функций
*/

implement main
  open core, console, string, list

domains
  token = val(value); op(operator); com(command); name(string).
  value = number(integer).
  operator = lbracket; rbracket; mult; divi; plus; minus.
  command = write; let; equal. %РАЗБЕЙ НА РАЗНЫЕ ДОМЕНЫ
  line = let(string Name, expression); write(expression).
  expression = token*.
class predicates
  scanner:(string) -> token*.
  makeToken:(string) -> token.
  getLines:(token* Input) -> line*.
  getExpression:(token* Input, token* ExprAcc, token* Expr [out], token* Rest [out]).
  toReversePolish:(token* Input, token* Stack, token* OutputAcc) -> token*.
  priority:(operator) -> integer.
  exeFunc:(line*).
  calculate:(token*, value* Stack) -> value.
  operation:(operator, value*) -> value.
  arity:(operator) -> integer.

class facts
  var:(string Name, value).

clauses
  % СОСТАВЛЯЕМ СПИСОК ТОКЕНОВ
  scanner(S) = [makeToken(Tok)|scanner(Rest)]:- frontToken(S, Tok, Rest), !.
  scanner(_) = [].

  makeToken("(") = op(lbracket) :- !.
  makeToken(")") = op(rbracket) :- !.
  makeToken("*") = op(mult) :- !.
  makeToken("/") = op(divi) :- !.
  makeToken("+") = op(plus) :- !.
  makeToken("-") = op(minus) :- !.
  makeToken("=") = com(equal) :- !.
  makeToken("write") = com(write) :- !.
  makeToken("let") = com(let) :- !.
  makeToken(S) = val(number(Num)) :- Num = tryToTerm(S), !.
  makeToken(S) = name(S) :- isName(S), !.
  makeToken(S) = _ :- exception::raise_user(write("Неизвестный токен ", S)).

  %ПОЛУЧАЕМ СТРОКИ ФУНКЦИИ В УДОБНОЙ ФОРМЕ
  getLines(Tokens) = [let(Name, Expression)|getLines(Rest)] :-
    split(3, Tokens, Left, Right),
    Left = [com(let), name(Name), com(equal)],
    getExpression(Right, [], Expression, Rest), !.
  getLines(Tokens) = [write(Expression)|getLines(Rest)] :-
    split(1, Tokens, Left, Right),
    Left = [com(write)],
    getExpression(Right, [], Expression, Rest), !.
  getLines([]) = [] :- !.
  getLines(Tokens) = _ :-
    exception::raise_user(write("Неожиданный участок программы:", Tokens)).

  %считываем токены, пока не наткнёмся на начало новой строки. Тогда преобразуем накопленное в ПОЛИЗ
  getExpression([], Expr, toReversePolish(reverse(Expr), [],[]), []) :- !.
  getExpression(Tokens, Expr, toReversePolish(reverse(Expr),[],[]), Tokens) :-
    (Tokens = [com(let)|_], !; Tokens = [com(write)|_]),
    write("Было:", Expr), nl, write("Стало:", toReversePolish(reverse(Expr), [],[])), nl, !.
  getExpression([T|Tokens], ExprAcc, Expression, Rest) :-
    getExpression(Tokens, [T|ExprAcc], Expression, Rest).

  % ПРЕОБРАЗУЕМ В ПОЛИЗ
  % числа или переменные записываем напрямую
  toReversePolish([V|Tokens], Stack, Output) =
    toReversePolish(Tokens, Stack, [V | Output]) :- V = val(_), !; V = name(_), !.
  % если стек пуст, то просо ложим в него оператор
  toReversePolish([Op|Tokens], [], Output) =
    toReversePolish(Tokens, [Op], Output) :- !.
  % левая скобка всегда ложится в стек
  toReversePolish([op(lbracket)|Tokens], Stack, Output) =
    toReversePolish(Tokens, [op(lbracket)|Stack], Output) :- !.
  % правая скобка выталкивает всё из стека, пока не натолкнётся на левую скобку
  toReversePolish([op(rbracket)|Tokens], [op(lbracket)|Stack], Output) =
    toReversePolish(Tokens, Stack, Output) :- !.
  toReversePolish([op(rbracket)|Tokens], [Op|Stack], Output) =
    toReversePolish([op(rbracket)|Tokens], Stack, [Op|Output]) :- !.
  % если приоритет оператора <= оператора на стеке, то он выталкивает оператор
  toReversePolish([op(InOp)|Tokens], [op(StOp)|Stack], Output) =
    toReversePolish([op(InOp)|Tokens], Stack, [op(StOp)|Output]) :- priority(InOp) <= priority(StOp), !.
  % иначе, оператор ложится на стек
  toReversePolish([InOp|Tokens], [StOp|Stack], Output) =
    toReversePolish(Tokens, [InOp|[Stop|Stack]], Output) :- !.
  % если вход пуст, выталкиваем из стека все операторы
  toReversePolish([], [Op|Stack], Output) =
    toReversePolish([], Stack, [Op | Output]) :- !.
  toReversePolish([],[], Output) = list::reverse(Output).

  priority(lbracket) = 0 :- !.
  priority(rbracket) = 1 :- !.
  priority(plus) = 2 :- !.
  priority(minus) = 2 :- !.
  priority(mult) = 3 :- !.
  priority(divi) = 3 :- !.

  %ВЫПОЛНЯЕМ ФУНКЦИЮ (список строк)
  exeFunc([let(Name, Expression) | Lines]) :-
    assert(var(Name, calculate(Expression, []))), exeFunc(Lines), !.
  exeFunc([write(Expression) | Lines]) :-
    Res = calculate(Expression, []),
    Res = number(V),
    write(V), nl, exeFunc(Lines), !.
  exeFunc([]).

  %ВЫЧИСЛИТЕЛЬ
  %просто число ложим на стек
  calculate([val(number(X))|Tokens], Stack) = calculate(Tokens, [number(X)|Stack]) :- !.
  %из переменной извлекаем число
  calculate([name(Name)|Tokens], Stack) =
    calculate(Tokens, [number(X)|Stack]) :- var(Name, number(X)), !.
  calculate([op(Op)|Tokens], Stack) =
    calculate(Tokens, [operation(Op, Operands)|RestStack]) :-
    N = arity(Op), split(N, Stack, Operands, RestStack), !.
  calculate([T|_], _) = _ :- exception::raise_user(write("Неожиданный токен ", T, "!")).
  calculate([], [number(Result)]) = number(Result) :- !.
  calculate([], _) = _ :-
    exception::raise_user("Операндов больше, чем требуют операторы выражения!").

  operation(plus, [number(A), number(B)]) = number(B+A) :- !.
  operation(minus, [number(A), number(B)]) = number(B-A) :- !.
  operation(mult, [number(A), number(B)]) = number(B*A) :- !.
  operation(divi, [number(A), number(B)]) = number(B div A) :- !.
  operation(Op,Vals) = _ :-
    exception::raise_user(write(
      "Неверное использование операции. Операция: ", Op, " Параметры: ", Vals)).

  arity(plus) = 2 :- !.
  arity(minus) = 2 :- !.
  arity(mult) = 2 :- !.
  arity(divi) = 2 :- !.
  arity(Op) = _ :- exception::raise_user(write("Неверное использование оператора ", Op, ".")).

  run() :-
    Source = file::readString("program.txt"),
    RawTokens = scanner(Source),
    write(RawTokens), nl,
    Lines = getLines(RawTokens),
    write("Строки: "), nl,
    write(Lines), nl,
    exeFunc(Lines),
    succeed. % place your own code here

end implement main

goal
  console::run(main::run).