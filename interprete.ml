(* Criando "aliases" para os módulos. *)
module Amb = AmbInterp
module A = Ast
module S = Sast
module T = Tast


(* Definindo uma exceção para o módulo. Ela será usada de outra forma, em vez de tratamento *)
(* de erros.                                                                                *)
exception Valor_de_retorno of T.expressao


(* Obtem o tipo  e o nome de uma variavel. *)
let obtem_nome_tipo_var exp =
    let open T in
    match exp with
    | ExpVar (v,tipo) ->
       (match v with
        | A.VarSimples (nome,_) -> (nome,tipo)
        | _ -> failwith "obtem_nome_tipo_var: nao implementado.")
    | _ -> failwith "obtem_nome_tipo_var: nao eh uma variavel."


(* Funções para extrair os valores de tipos primitivos *)
let pega_int exp =
    match exp with
    | T.ExpInt (i,_) -> i
    | _ -> failwith "pega_int: nao eh um inteiro."


let pega_float exp =
    match exp with
    | T.ExpFloat (f,_) -> f
    | _ -> failwith "pega_float: nao eh um float."


let pega_bool exp =
    match exp with
    | T.ExpBool (b,_) -> b
    | _ -> failwith "pega_bool: nao eh um booleano."


let pega_string exp =
    match exp with
    | T.ExpString (s,_) -> s
    | _ -> failwith "pega_string: nao eh uma string."


let pega_char exp =
    match exp with
    | T.ExpChar (c,_) -> c
    | _ -> failwith "pega_char: nao eh um char."


(* Classes dos operadores da mini linguagem *)
type classe_op = Aritimetico
    | Relacional
    | Logico


(* Dado um operador, retorna a classe a qual ele pertence. *)
let classifica op = let open A in
    match op with
    | Ou
    | E -> Logico
    | Menor
    | Maior
    | MenorIgual
    | MaiorIgual
    | Igual
    | Difer -> Relacional
    | Soma
    | Sub
    | Mult
    | Div
    | Mod -> Aritimetico


(* Interpreta uma expressão e retorna o seu valor após ela ser avaliada *)
let rec interpreta_exp amb exp =
    let open A in
    let open T in
    match exp with
    | ExpVar _ ->
        let id, tipo = obtem_nome_tipo_var exp in
        (* Tenta encontrar o valor da variável no escopo local, se não            *)
        (* encontrar, tenta novamente no escopo que engloba o atual. Prossegue-se *)
        (* assim até encontrar o valor em algum escopo englobante ou até          *)
        (* encontrar o escopo global. Se em algum lugar for encontrado,           *)
        (* devolve-se o valor. Em caso contrário, devolve uma exceção             *)
       (match (Amb.busca amb id) with
        | Amb.EntVar (tipo,v) ->
           (match v with
            | None -> failwith ("Variavel nao inicializada: " ^ id)
            | Some valor -> valor)
        | _ -> failwith "interpreta_exp: expvar")

    (* Avaliando as expressões primitivas da mini linguagem. *)
    | ExpInt _
    | ExpFloat _
    | ExpBool _
    | ExpString _
    | ExpChar _
    | ExpVoid -> exp

    (* Avaliando as expressões com operador binário *)
    | ExpOp ((op,top),(esq,tesq),(dir,tdir)) ->
        (* Interpretando as expressões à direita e à esquerda do operador da expressão. *)
        let vesq = interpreta_exp amb esq
        and vdir = interpreta_exp amb dir in

        (* Avalia e retorna o valor de uma expressão aritimética. *)
        let interpreta_aritimetico () =
           (match tesq with
            | Int ->
               (match op with
                | Soma -> ExpInt (pega_int vesq + pega_int vdir, top)
                | Sub -> ExpInt (pega_int vesq - pega_int vdir, top)
                | Div -> ExpInt (pega_int vesq / pega_int vdir, top)
                | Mult -> ExpInt (pega_int vesq * pega_int vdir, top)
                | Mod -> ExpInt (pega_int vesq mod pega_int vdir, top)
                | _ -> failwith "interpreta_aritimetico: int")
            | Float ->
               (match op with
                | Soma -> ExpFloat (pega_float vesq +. pega_float vdir, top)
                | Sub -> ExpFloat (pega_float vesq -. pega_float vdir, top)
                | Div -> ExpFloat (pega_float vesq /. pega_float vdir, top)
                | Mult -> ExpFloat (pega_float vesq *. pega_float vdir, top)
                | _ -> failwith "interpreta_aritimetico: float")
            | String ->
               (match op with
                | Soma -> ExpString (pega_string vesq ^ pega_string vdir, top)
                | _ -> failwith "interpreta_aritimetico: string")
            | _ -> failwith "interpreta_aritimetico")

        (* Avalia e retorna o valor de uma expressão relacional. *)
        and interpreta_relacional () =
           (match tesq with
            | Int ->
               (match op with
                | Maior -> ExpBool (pega_int vesq > pega_int vdir, top)
                | Menor -> ExpBool (pega_int vesq < pega_int vdir, top)
                | MaiorIgual -> ExpBool (pega_int vesq >= pega_int vdir, top)
                | MenorIgual -> ExpBool (pega_int vesq <= pega_int vdir, top)
                | Igual -> ExpBool (pega_int vesq = pega_int vdir, top)
                | Difer -> ExpBool (pega_int vesq <> pega_int vdir, top)
                | _ -> failwith "interpreta_relacional: int")
            | Float ->
               (match op with
                | Maior -> ExpBool (pega_float vesq > pega_float vdir, top)
                | Menor -> ExpBool (pega_float vesq < pega_float vdir, top)
                | MaiorIgual -> ExpBool (pega_float vesq <= pega_float vdir, top)
                | MenorIgual -> ExpBool (pega_float vesq >= pega_float vdir, top)
                | Igual -> ExpBool (pega_float vesq = pega_float vdir, top)
                | Difer -> ExpBool (pega_float vesq <> pega_float vdir, top)
                | _ -> failwith "interpreta_relacional: float")
            | String ->
               (match op with
                | Igual -> ExpBool (pega_string vesq = pega_string vdir, top)
                | Difer -> ExpBool (pega_string vesq <> pega_string vdir, top)
                | _ -> failwith "interpreta_relacional: string")
            | Char ->
               (match op with
                | Igual -> ExpBool (pega_char vesq = pega_char vdir, top)
                | Difer -> ExpBool (pega_char vesq <> pega_char vdir, top))
            | _ -> failwith "interpreta_relacional")

        (* Avalia e retorna o valor de uma exoressão lógica *)
        and interpreta_logico () =
           (match tesq with
            | Bool ->
               (match op with
                | E -> ExpBool (pega_bool vesq && pega_bool vdir, top)
                | Ou -> ExpBool (pega_bool vesq || pega_bool vdir, top)
                | _ -> failwith "interpreta_logico: bool")
            | _ -> failwith "interpreta_logico")
        in
        let valor =
           (match (classifica op) with
            | Aritimetico -> interpreta_aritimetico ()
            | Relacional -> interpreta_relacional ()
            | Logico -> interpreta_logico ())
        in
        valor

    (* Avalia uma expressão unária. *)
    | ExpUn ((op,top),(dir,tdir)) ->
        (* Interpreta a expressão à direita do operador *)
        let vdir = interpreta_exp amb dir in
       (match tdir with
        | Int ->
           (match op with
            | UMenos -> ExpInt ((-1) * pega_int vdir, top)
            | _ -> failwith "expun: inteiro")
        | Float ->
           (match op with
            | UMenos -> ExpFloat ((-1.0) *. pega_float vdir, top)
            | _ -> failwith "expun: float")
        | Bool ->
           (match op with
            | Not ->
                let b = pega_bool vdir in
                ExpBool (not (b), top))
        | _ -> failwith "expfun")

    (* Avalia uma chamada de função *)
    | ExpFun (id,args,tipo) ->
        let open Amb in
       (match (Amb.busca amb id) with
        | Amb.EntFun {tipo_fn; formais; locais; corpo} ->
            (* Interpreta cada um dos argumentos *)
            let vargs = List.map (interpreta_exp amb) args in
            (* Associa os argumentos aos parâmetros formais *)
            let vformais = List.map2 (fun (n,t) v -> (n, t, Some v)) formais vargs
            in interpreta_fun amb id vformais locais corpo
        | _ -> failwith "interpreta_exp: expchamada")

    | _ -> failwith "interpreta_exp: nao implementado"

(* Interpreta uma função *)
and interpreta_fun amb fn_nome fn_formais fn_locais fn_corpo =
    let open A in
    (* Estende o ambiente global, adicionando um ambiente local *)
    let ambfn = Amb.novo_escopo amb in
    let insere_local d =
        match d with
        | (DecVar (v,t)) -> Amb.insere_local ambfn (fst v)  t None
    in
    (* Associa os argumentos aos parâmetros e insere no novo ambiente *)
    let insere_parametro (n,t,v) = Amb.insere_param ambfn n t v in
    let _ = List.iter insere_parametro fn_formais in
    (* Insere as variáveis locais no novo ambiente *)
    let _ = List.iter insere_local fn_locais in
    (* Interpreta cada comando presente no corpo da função usando o novo *)
    (* ambiente                                                          *)
    try
        let _ = List.iter (interpreta_cmd ambfn) fn_corpo in T.ExpVoid
    with Valor_de_retorno expret ->
        expret

(* Interpreta os comandos da mini linguagem *)
and interpreta_cmd amb cmd =
    let open A in
    let open T in
    match cmd with
    | CmdAtrib (elem,exp) ->
        (* Interpreta o lado direito da atribuição *)
        let exp = interpreta_exp amb exp
        (* Faz o mesmo para o lado esquerdo *)
        and (elem1,tipo) = obtem_nome_tipo_var elem in
        Amb.atualiza_var amb elem1 tipo (Some exp)

    (* Implementando os comandos de leitura *)
    | CmdReadInt elem ->
        let (elem1,tipo) = obtem_nome_tipo_var elem in
        let valor = T.ExpInt (read_int (), tipo) in
        Amb.atualiza_var amb elem1 tipo (Some valor)

    | CmdReadFloat elem ->
        let (elem1,tipo) = obtem_nome_tipo_var elem in
        let valor = T.ExpFloat (read_float (), tipo) in
        Amb.atualiza_var amb elem1 tipo (Some valor)

    | CmdReadString elem ->
        let (elem1,tipo) = obtem_nome_tipo_var elem in
        let valor = T.ExpString (read_line (), tipo) in
        Amb.atualiza_var amb elem1 tipo (Some valor)

    | CmdReadChar elem ->
        let (elem1,tipo) = obtem_nome_tipo_var elem in
        let valor = T.ExpChar ((read_line ()).[0], tipo) in
        Amb.atualiza_var amb elem1 tipo (Some valor)

    | CmdWhile (teste,corpo) ->
        (* Criando uma função recursiva para simular o loop do while. *)
        let rec iteracao amb teste corpo =
            (* Antes de "executar" o corpo do while, primeiro devemos *)
            (* avaliar o teste.                                       *)
            let vteste = interpreta_exp amb teste in
           (match vteste with
            | ExpBool (true,_) ->
                (* Interpretando os comandos do corpo do while *)
                let _ = List.iter (interpreta_cmd amb) corpo
                in
                (* Repetindo o laço while *)
                iteracao amb teste corpo
            | _ -> ())
        in
        iteracao amb teste corpo

    | CmdFor (inicio,teste,fim,corpo) ->
        (* "Traduzindo" o for para o seu equivalente while antes de *)
        (* interpretar.                                             *)
        let _ = interpreta_cmd amb inicio in
        let comando = CmdWhile (teste,corpo @ [fim]) in
        interpreta_cmd amb comando

    | CmdIf (teste,entao,senao) ->
        let teste1 = interpreta_exp amb teste in
       (match teste1 with
        | ExpBool (true,_) ->
            (* Interpreta cada comando do bloco 'então' *)
            List.iter (interpreta_cmd amb) entao
        | _ ->
            (* Interpreta cada comando do bloco 'senão', se houver *)
           (match senao with
            | None -> ()
            | Some bloco -> List.iter (interpreta_cmd amb) bloco))

    | CmdPrint exps ->
        (* Interpreta cada argumento da função 'saida' *)
        let exps = List.map (interpreta_exp amb) exps in
        let imprima exp =
           (match exp with
            | T.ExpInt (n,_) -> let _ = print_int n in print_string " "
            | T.ExpFloat (f,_) -> let _ = print_float f in print_string " "
            | T.ExpString (s,_) -> let _ = print_string s in print_string " "
            | _ -> failwith "imprima: nao implementado")
        in
        let _ = List.iter imprima exps in
        print_newline ()

    | CmdReturn exp ->
        (* Levantar uma exceção foi necessária pois, pela semântica do comando de   *)
        (* retorno, sempre que ele for encontrado em uma função, a computação       *)
        (* deve parar retornando o valor indicado, sem realizar os demais comandos. *)
       (match exp with
        (* Se a função não retornar nada, então retorne ExpVoid *)
        | None -> raise (Valor_de_retorno ExpVoid)
        | Some e ->
            (* Avalia a expressão e retorne o resultado *)
            let e1 = interpreta_exp amb e in
            raise (Valor_de_retorno e1))

    | CmdSwitch (v,cases,default) ->
        let (v1,tipo) = obtem_nome_tipo_var v in
        (* Interpreta os comandos dentro de um case *)
        let interpreta_case case =
           (match case with
            |Case (exp, comandos) ->
                let teste = interpreta_exp amb (ExpOp((Igual,Bool),(v,tipo),(exp,tipo))) in
               (match teste with
                | ExpBool (true,_) ->
                    List.iter (interpreta_cmd amb) comandos; true
                | _ -> false))
        in
        (* Percorre cada "case" do comando switch e verifica qual deles será executado. *)
        let rec interpreta_cases cases =
           (match cases with
            | c :: cs -> 
                let res = interpreta_case c in
                (* Verifica se o case foi executado com sucesso. *)
                if res then true
                (* Caso contrário, passa para o próximo case *)
                else interpreta_cases cs
            | [] -> false)
        in
        let res = interpreta_cases cases in
        if res then ()
        else
           (match default with
            | None -> ()
            | Some (Default bloco) ->  List.iter (interpreta_cmd amb) bloco)
    
    | CmdFun exp -> ignore (interpreta_exp amb exp)

    | _ -> failwith "interpreta_cmd: nao implementado"


let insere_declaracao_var amb dec =
    match dec with
        A.DecVar (nome, tipo) ->  Amb.insere_local amb (fst nome) tipo None

let insere_declaracao_fun amb dec =
  let open A in
    match dec with
      DecFun {fn_nome; fn_tiporet; fn_formais; fn_locais; fn_corpo} ->
        let nome = fst fn_nome in
        let formais = List.map (fun (n,t) -> ((fst n), t)) fn_formais in
        Amb.insere_fun amb nome formais fn_locais fn_tiporet fn_corpo


(* Lista de cabeçalhos das funções pré definidas *)
let fn_predefs = let open A in [
    ("entrada", [("x", Int); ("y", Int)], Void, []);
    ("saida",     [("x", Int); ("y", Int)], Void, []);
]

(* insere as funções pré definidas no ambiente global *)
let declara_predefinidas amb =
  List.iter (fun (n,ps,tr,c) -> Amb.insere_fun amb n ps [] tr c) fn_predefs

let interprete ast =
  (* cria ambiente global inicialmente vazio *)
  let amb_global = Amb.novo_amb [] in
  let _ = declara_predefinidas amb_global in
  let (A.Programa (decs_globais, decs_funs, corpo)) = ast in
  let _ = List.iter (insere_declaracao_var amb_global) decs_globais in
  let _ = List.iter (insere_declaracao_fun amb_global) decs_funs in
  (* Interpreta a função principal *)
  let resultado = List.iter (interpreta_cmd amb_global) corpo in
  resultado

