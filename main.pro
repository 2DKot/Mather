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
  token = val(value); op(operator); com(command); name(string); fun; comma;
          rawIf; rawElse; rawEndif.
  value = number(integer); bool(boolean).
  operator = lbracket; rbracket; mult; divi; plus; minus;
              equal; greater; less; l_or; l_and; func(string).
  command =  write; let; return; ifGoto(integer); goto(integer); label(integer). %РАЗБЕЙ НА РАЗНЫЕ ДОМЕНЫ
  line = let(string Name, expression); write(expression); return(expression);
          ifGoto(expression, integer); goto(integer); label(integer).
  expression = token*.
class predicates
  toB:(predicate_dt{})->value.

  scanner:(string) -> token*.
  makeToken:(string) -> token.
  correctFunCalls:(token*, token*) -> token*.
  correctParams:(token*, token*) -> token*.
  getCallParams:(token*, token*, token*[out], token*[out], integer).
  correctIfs:(token*, token*, integer, integer*) -> token*.
  declareFuns:(token*).
  getFunParams:(token*, string*, string* [out], token* [out]).
  getFunTokens:(token*, token*) -> token* nondeterm.
  getLines:(token* Input) -> line*.
  getExpression:(token* Input, token* ExprAcc, token* Expr [out], token* Rest [out]).
  toReversePolish:(token* Input, token* Stack, token* OutputAcc) -> token*.
  priority:(operator) -> integer.
  exeFunc:(line*, string FunName) -> value.
  skipToLabel:(line*, integer) -> line*.
  writeValue:(value).
  calculate:(token*, value* Stack, string FunName) -> value.
  operation:(operator, value*) -> value.
  arity:(operator) -> integer.

class facts
  var:(string Name, value, string FunName).
  fun:(string Name, line*, string* Params).

clauses
  toB(P) = bool(true) :- P(), !.
  toB(_) = bool(false).

  % СОСТАВЛЯЕМ СПИСОК ТОКЕНОВ
  scanner(S) = [makeToken(Tok)|scanner(Rest)]:- frontToken(S, Tok, Rest), !.
  scanner(_) = [].

  makeToken("(") = op(lbracket) :- !.
  makeToken(")") = op(rbracket) :- !.
  makeToken("*") = op(mult) :- !.
  makeToken("/") = op(divi) :- !.
  makeToken("+") = op(plus) :- !.
  makeToken("-") = op(minus) :- !.
  makeToken("=") = op(equal) :- !.
  makeToken(">") = op(greater) :- !.
  makeToken("<") = op(less) :- !.
  makeToken("|") = op(l_or) :- !.
  makeToken("&") = op(l_and) :- !.
  makeToken(",") = comma :- !.
  makeToken("write") = com(write) :- !.
  makeToken(":") = com(let) :- !.
  makeToken("return") = com(return) :- !.
  makeToken("if") = rawIf :- !.
  makeToken("else") = rawElse :- !.
  makeToken("endif") = rawEndif :- !.
  makeToken("true") = val(bool(true)) :- !.
  makeToken("false") = val(bool(false)) :- !.
  makeToken("fun") = fun :- !.
  makeToken(S) = val(number(Num)) :- Num = tryToTerm(S), !.
  makeToken(S) = name(S) :- isName(S), !.
  makeToken(S) = _ :- exception::raise_user(write("Неизвестный токен ", S)).

  correctFunCalls([], NewTokens) = reverse(NewTokens) :- !.
  correctFunCalls(RawTokens, NewTokens) =
    correctFunCalls(append(CorrectedParams,Rest), append(NewCall,NewTokens))
    :- % встретили вызов функции
    split(2, RawTokens, Left, Right),
    Left = [name(Name), op(lbracket)],
    getCallParams(Right, [], Params, Rest, 1),
    CorrectedParams = append(correctParams(Params, []),[op(rbracket)]),
    %nl,write("CorrectedParams: ", CorrectedParams), nl,
    NewCall = reverse([op(lbracket), op(func((Name))), op(lbracket)]),
    !.
  correctFunCalls([Tok|RawTokens], NewTokens) = correctFunCalls(RawTokens, [Tok|NewTokens]).

  correctParams([], NewTokens) = NewTokens :- !.
  correctParams([comma|Tokens], NewTokens) =
    correctParams(Tokens, [op(rbracket)|[op(lbracket)|NewTokens]]):- !.
  correctParams([Tok|Tokens], NewTokens) =
    correctParams(Tokens, [Tok|NewTokens]) :- !.

  getCallParams(Tokens, ParamsAcc, ParamsAcc, Tokens, 0) :- !.
  getCallParams([op(lbracket)|Tokens], ParamsAcc, Params, Rest, Balance) :-
    getCallParams(Tokens, [op(lbracket)|ParamsAcc], Params, Rest, Balance+1), !.
  getCallParams([op(rbracket)|Tokens], ParamsAcc, Params, Rest, Balance) :-
    getCallParams(Tokens, [op(rbracket)|ParamsAcc], Params, Rest, Balance-1), !.
  getCallParams([Tok|Tokens], ParamsAcc, Params, Rest, Balance) :-
    getCallParams(Tokens, [Tok|ParamsAcc], Params, Rest, Balance), !.
  getCallParams([], _, _, _, _) :-
    exception::raise_user("Неверная расстановка скобок в вызове функции!").

  correctIfs([], NewTokens, _, _) = reverse(NewTokens) :- !.
  correctIfs([rawIf|Tokens], NewTokens, MaxLabel, Stack) =
    correctIfs(Tokens, [com(ifGoto(MaxLabel))|NewTokens], MaxLabel+1, [MaxLabel|Stack]) :- !.
  correctIfs([rawElse|Tokens], NewTokens, MaxLabel, [Top|Stack]) =
    correctIfs(Tokens,
      append([com(label(Top))], [com(goto(MaxLabel))], NewTokens),
      MaxLabel+1,
      [MaxLabel|Stack]) :- !.
  correctIfs([rawEndif|Tokens], NewTokens, MaxLabel, [Top|Stack]) =
    correctIfs(Tokens, [com(label(Top))|NewTokens], MaxLabel, Stack) :- !.
  correctIfs([Tok|Tokens], NewTokens, MaxLabel, Stack) =
    correctIfs(Tokens, [Tok|NewTokens], MaxLabel, Stack) :- !.

  declareFuns(RawTokens) :-
    write("Объявлены функции:"), nl,
    FunAllTokens = getFunTokens(list::drop(1,RawTokens), []),
    getFunParams(FunAllTokens, [], NP, Tokens),
    [Name | Params] = NP,
    Lines = getLines(Tokens),
    assert(fun(Name, Lines, Params)),
    write(Name, " ", Params), nl,
    fail; succeed.

  getFunParams([com(let) | Tokens], AccParams, reverse(AccParams), Tokens) :- !.
  getFunParams([name(Name) | Tokens], AccParams, Params, Rest) :-
    getFunParams(Tokens, [Name|AccParams], Params, Rest), !.
  getFunParams([Tok|_], _, _, _) :-
    exception::raise_user(write("Ожидалось имя параметра функции, а получено", Tok)).
  getFunParams([], _, _, _) :-
    exception::raise_user("Функция внезапно оборвалась!").

  getFunTokens([], Acc) = reverse(Acc) :- !.
  getFunTokens([fun|_], Acc) = reverse(Acc).
  getFunTokens([fun|Tokens], _) = getFunTokens(Tokens, []) :- !.
  getFunTokens([Tok|Tokens], Acc) = getFunTokens(Tokens, [Tok|Acc]) :- !.

  %ПОЛУЧАЕМ СТРОКИ ФУНКЦИИ В УДОБНОЙ ФОРМЕ
  getLines(Tokens) = [let(Name, Expression)|getLines(Rest)] :- %переменная
    split(2, Tokens, Left, Right),
    Left = [name(Name), com(let)],
    getExpression(Right, [], Expression, Rest), !.
  getLines(Tokens) = [write(Expression)|getLines(Rest)] :- %вывод на экран
    split(1, Tokens, Left, Right),
    Left = [com(write)],
    getExpression(Right, [], Expression, Rest), !.
  getLines(Tokens) = [return(Expression)|getLines(Rest)] :- %возврат значения
    split(1, Tokens, Left, Right),
    Left = [com(return)],
    getExpression(Right, [], Expression, Rest), !.
  getLines(Tokens) = [ifGoto(Expression, LabelNumber)|getLines(Rest)] :- %if
    split(1, Tokens, Left, Right),
    Left = [com(ifGoto(LabelNumber))],
    getExpression(Right, [], Expression, Rest), !.
  getLines([com(goto(I))|Tokens]) = [goto(I)|getLines(Tokens)] :- !.%goto
  getLines([com(label(I))|Tokens]) = [label(I)|getLines(Tokens)] :- !.%label
  getLines([]) = [] :- !.
  getLines(Tokens) = _ :-
    exception::raise_user(write("Неожиданный участок программы:", Tokens)).

  %считываем токены, пока не наткнёмся на начало новой строки. Тогда преобразуем накопленное в ПОЛИЗ
  getExpression([], Expr, toReversePolish(reverse(Expr), [],[]), []) :- !.
  getExpression(Tokens, Expr, toReversePolish(reverse(Expr),[],[]), Tokens) :-
    (Tokens = [name(_)|[com(let)|_]], !; Tokens = [com(_)|_]),
    %write("Было:", Expr), nl, write("Стало:", toReversePolish(reverse(Expr), [],[])), nl,
    !.
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
  priority(l_or) = 2 :- !.
  priority(l_and) = 3 :- !.
  priority(equal) = 4 :- !.
  priority(less) = 4 :- !.
  priority(greater) = 4 :- !.
  priority(plus) = 5 :- !.
  priority(minus) = 5 :- !.
  priority(mult) = 6 :- !.
  priority(divi) = 6 :- !.
  priority(func(_)) = 10 :- !.

  %ВЫПОЛНЯЕМ ФУНКЦИЮ (список строк)
  exeFunc([let(Name, Expression) | Lines], FunName) = exeFunc(Lines, FunName) :-
    assert(var(Name, calculate(Expression, [], FunName), FunName)), !.
  exeFunc([write(Expression) | Lines], FunName) = exeFunc(Lines, FunName) :-
    Res = calculate(Expression, [], FunName),
    writeValue(Res), !.
  exeFunc([return(Expression) | _], FunName) = Result :-
    Result = calculate(Expression, [], FunName),
    (
      fun(FunName, _, Params), !;
      exception::raise_user("Функция была удаления во время её исполнения. Ты добился невозможного!")
    ),
    forAll(Params, {(Param) :- retract(var(Param,_,FunName)), !;
      exception::raise_user(write("Ошибка удаления переменной ", Param,
        " при выходе из контекста ", FunName))}),
    !.
  exeFunc([ifGoto(Expression, LabelNumber) | Lines], FunName) = exeFunc(Rest, FunName) :-
    Res = calculate(Expression, [], FunName),
    (
      Res = bool(false),
      Rest = skipToLabel(Lines, LabelNumber), !;
      Res = bool(true),
      Rest = Lines, !;
      exception::raise_user(write("В if ожидалось булевое значение. Получено ", Res, "."))
    ), !.
  exeFunc([goto(LabelNumber) | Lines], FunName) = exeFunc(Rest, FunName) :-
    Rest = skipToLabel(Lines, LabelNumber), !.
  exeFunc([label(_) | Lines], FunName) = exeFunc(Lines, FunName) :- !.
  exeFunc([], _) = _ :- exception::raise_user("Функция должна возвращать значение!").

  skipToLabel([label(LabelNumber)|Lines], LabelNumber) = Lines :- !.
  skipToLabel([_|Lines], LabelNumber) = skipToLabel(Lines, LabelNumber) :- !.
  skipToLabel([], LabelNumber) = _ :-
    exception::raise_user(write("Программа оборвалась до того, как появилась метка ", LabelNumber,
      ". Забыли endif?")).

  writeValue(number(V)) :- write(V), nl, !.
  writeValue(bool(V)) :- write(V), nl, !.

  %ВЫЧИСЛИТЕЛЬ
  %просто число ложим на стек
  calculate([val(V)|Tokens], Stack, FunName) = calculate(Tokens, [V|Stack], FunName) :- !.
  %из переменной извлекаем число
  calculate([name(Name)|Tokens], Stack, FunName) =
    calculate(Tokens, [V|Stack], FunName) :- var(Name, V, FunName), !.
  calculate([op(Op)|Tokens], Stack, FunName) =
    calculate(Tokens, [operation(Op, Operands)|RestStack], FunName) :-
    N = arity(Op), split(N, Stack, Operands, RestStack), !.
  calculate([T|_], _, _) = _ :- exception::raise_user(write("Неожиданный токен ", T, "!")).
  calculate([], [V], _) = V :- !.
  calculate([], _, _) = _ :-
    exception::raise_user("Операндов больше, чем требуют операторы выражения!").

  operation(plus, [number(A), number(B)]) = number(B+A) :- !.
  operation(minus, [number(A), number(B)]) = number(B-A) :- !.
  operation(mult, [number(A), number(B)]) = number(B*A) :- !.
  operation(divi, [number(A), number(B)]) = number(B div A) :- !.
  operation(equal, [number(A), number(B)]) = toB({:-B=A}) :- !.
  operation(greater, [number(A), number(B)]) = toB({:-B>A}) :- !.
  operation(less, [number(A), number(B)]) = toB({:-B<A}) :- !.
  operation(l_or, [bool(A), bool(B)]) = bool(boolean::logicalOr(B,A)) :- !.
  operation(l_and, [bool(A), bool(B)]) = bool(boolean::logicalAnd(B,A)) :- !.
  operation(func(FunName),Values) = exeFunc(Lines, FunName) :-
    fun(FunName, Lines, Params),
    Tuples = zip(Params, Values),
    forAll(Tuples,{(tuple(ParamName, Val)) :- assert(var(ParamName, Val, FunName))}),
    !.
  operation(Op,Vals) = _ :-
    exception::raise_user(write(
      "Неверное использование операции. Операция: ", Op, " Параметры: ", Vals)).

  arity(plus) = 2 :- !.
  arity(minus) = 2 :- !.
  arity(mult) = 2 :- !.
  arity(divi) = 2 :- !.
  arity(equal) = 2 :-!.
  arity(greater) = 2 :- !.
  arity(less) = 2 :- !.
  arity(l_or) = 2 :- !.
  arity(l_and) = 2 :- !.
  arity(func(Name)) = list::length(Params) :- fun(Name, _, Params), !.
  arity(Op) = _ :- exception::raise_user(write("Неверное использование оператора ", Op, ".")).

  run() :-
    Source = file::readString("program.txt"),
    RawTokens = scanner(Source),
    %write(RawTokens), nl,
    CorrectedCalls = correctFunCalls(RawTokens, []),
    %write("Исправленные вызовы: \n", CorrectedTokens),
    CorrectedIfs = correctIfs(CorrectedCalls, [], 0, []),
    %write("Исправленные ифы: \n", CorrectedIfs),
    declareFuns(CorrectedIfs),
    (fun("main", Lines, _), !; exception::raise_user("Отсутствует функция main!")),
    write("Начинаем выполнение программы."), nl,
    Code = exeFunc(Lines, "main"),
    write("Программа завершилась с кодом ", Code), nl,
    succeed. % place your own code here

end implement main

goal
  console::run(main::run).