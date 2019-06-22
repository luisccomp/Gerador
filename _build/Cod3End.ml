open Printf
open Ast
open Tast
open Codigo


(* Contador de temporários: controla quantos temporários foram usados até um dado *)
(* momento no gerador de código intermediário.                                    *)
let conta_temp = ref 0

(* Contador de rótulos: controla a quantidade de rótulos de um dado prefixo foram *)
(* usados no gerador de código intermediário.                                     *)
let conta_rotulos = ref (Hashtbl.create 5)


(* Zera os contadores de rótulos e de temporários. *)
let zera_contadores () =
    begin
        conta_temp := 0;
        conta_rotulos := Hashtbl.create 5;
    end


(* "Aloca" um novo temporário. *)
let novo_temp () =
    let numero = !conta_temp in
    let _ = incr conta_temp in
    Temp numero


(* "Aloca" um novo rótulo. Se ele não existir, cria uma nova entrada na tabela de *)
(* rótulos ou atualiza o contador de rótulos se este mesmo existe.                *)
let novo_rotulo prefixo =
    if Hashtbl.mem !conta_rotulos prefixo
    then
        let numero = Hashtbl.find !conta_rotulos prefixo in
        let _ = Hashtbl.replace !conta_rotulos prefixo (numero + 1) in
        Rotulo (prefixo ^ (string_of_int numero))
    else
        let _ = Hashtbl.add !conta_rotulos prefixo 1 in
        Rotulo (prefixo ^ "0")


(* Código para impressão. *)
let endr_to_str = function
    | Nome s -> s
    | ConstInt i -> string_of_int i
    | ConstFloat f -> string_of_float f
    | ConstBool b -> string_of_bool b
    | ConstString s -> s
    | ConstChar c -> sprintf "%c" c
    | Temp n -> "t" ^ string_of_int n


let tipo_to_str t =
    match t with
    | Int -> "int"
    | Float -> "float"
    | Char -> "char"
    | String -> "string"
    | Void -> "void"
    | Bool -> "bool"


let op_to_str op =
    match op with
    | Soma -> "+"
    | Sub -> "-"
    | Div -> "/"
    | Mult -> "-"
    | E -> "&&"
    | Ou -> "||"
    | Mod -> "%"
    | Maior -> ">"
    | Menor -> "<"
    | MaiorIgual -> ">="
    | MenorIgual -> "<="
    | Igual -> "=="
    | Difer -> "!="
    | Not -> "!"
    | UMenos -> "-"


let rec args_to_str ats =
    match ats with
    | [] -> ""
    | [(a,t)] ->
        let str = sprintf "(%s,%s)" (endr_to_str a) (tipo_to_str t) in
        str
    | (a,t) :: ats ->
        let str = sprintf "(%s,%s)" (endr_to_str a) (tipo_to_str t) in
        str ^ args_to_str ats


let rec escreve_cod3 c =
    match c with
    | AtribBin (x,y,op,z) ->
        sprintf "%s := %s %s %s\n" (endr_to_str x) 
                                   (endr_to_str y) 
                                   (op_to_str (fst op)) 
                                   (endr_to_str z)
    | AtribUn (x,op,y) ->
        sprintf "%s := %s %s\n" (endr_to_str x) 
                                (op_to_str (fst op)) 
                                (endr_to_str y)
    | Copia (x,y) ->
        sprintf "%s := %s\n" (endr_to_str x) (endr_to_str y)
    | Goto l ->
        sprintf "goto %s\n" (escreve_cod3 l)
    | If (x,l) ->
        sprintf "if %s goto %s\n" (endr_to_str x) (escreve_cod3 l)
    | IfFalse (x,l) ->
        sprintf "ifFalse %s goto %s\n" (endr_to_str x) (escreve_cod3 l)
    | IfRelgoto (x,oprel,y,l) ->
        sprintf "if %s %s %s goto %s\n" (endr_to_str x) 
                                        (op_to_str (fst oprel)) 
                                        (endr_to_str y) 
                                        (escreve_cod3 l)
    | Call (p,ats,t) -> sprintf "call %s(%s): %s\n" p (args_to_str ats) (tipo_to_str t)
    | Recebe (x,t) -> sprintf "recebe %s,%s\n" x (tipo_to_str t)
    | Local (x,t) -> sprintf "local %s,%s\n" x (tipo_to_str t)
    | Global (x,t) -> sprintf "global %s,%s\n" x (tipo_to_str t)
    | CallFn (x,p,ats,t) ->
        sprintf "%s := call %s(%s): %s\n" (endr_to_str x) p (args_to_str ats) (tipo_to_str t)
    | Return x ->
       (match x with
        | None -> "return\n"
        | Some x -> sprintf "return %s\n" (endr_to_str x))
    | BeginFun (id,np,nl) -> sprintf "beginFun %s(%d,%d)\n" id np nl
    | EndFun -> "endFun\n\n"
    | Rotulo r -> sprintf "%s: " r


let rec escreve_codigo cod =
    match cod with
    | [] -> printf "\n"
    | c :: cs ->
        printf "%s" (escreve_cod3 c); 
        escreve_codigo cs

(* Código do tradutor para código de 3 endereço *)

(* Retorna o tipo de uma expressão. *)
let pega_tipo exp =
    match exp with
    | ExpVar (_,t)
    | ExpInt (_,t)
    | ExpFloat (_,t)
    | ExpBool (_,t)
    | ExpString (_,t)
    | ExpChar (_,t)
    | ExpOp ((_,t),_,_)
    | ExpUn ((_,t),_)
    | ExpFun (_,_,t) -> t
    | _ -> failwith "pega_tipo: nao implementado"



let rec converte_if var cases default =
    match cases with
    | [] ->
        let corpo = (match default with
                     | None -> []
                     | Some (Default bloco) -> bloco)
        in
        CmdIf (ExpBool (true, Bool), corpo, None)

    | [Case (expr, corpo)] ->
        let tipo = pega_tipo var in
        let bloco = (match default with
                     | None -> None
                     | Some (Default bloco) -> Some bloco)
        in
        CmdIf (ExpOp ((Igual,Bool),(var,tipo),(expr,tipo)), corpo, bloco)

    | Case (expr, corpo) :: cases ->
        let tipo = pega_tipo var in
        CmdIf (ExpOp ((Igual, Bool), (var,tipo), (expr,tipo)), corpo, Some [converte_if var cases default])


let converte_switch_if cmd =
    match cmd with
    | CmdSwitch (var, cases, default) ->
        converte_if var cases default
    | _ -> failwith "So aceita comando switch"



(* Traduz uma expressão para a sua equivalente em código de 3 endereços. *)
let rec traduz_exp exp =
    match exp with
    (* Tratando as variáveis. Na minha mini linguagem só existe o tipo varsimples. *)
    | ExpVar (v,tipo) ->
       (match v with
        | VarSimples nome ->
            let id = fst nome in
            (Nome id, [])
        (*| _ -> failwith "traduz_exp (expvar): nao implementado"*))

    | ExpInt (n,Int) ->
        (* Para uma expressão inteiro usada fora de uma atribuição (ex: "x=10;")  *)
        (* é criado um novo temporário para a mesma antes de usá-la em uma        *)
        (* expressão.                                                             *)
        let t = novo_temp () in
        (t, [Copia (t, ConstInt n)])

    | ExpFloat (n, Float) ->
        (* Da memsa forma que as expressões inteiras, o mesmo método é utilizado  *)
        (* para as expressões float.                                              *)
        let t = novo_temp () in
        (t, [Copia (t, ConstFloat n)])

    | ExpBool (n, Bool) ->
        let t = novo_temp () in
        (t, [Copia (t, ConstBool n)])

    | ExpString (n, String) ->
        let t = novo_temp () in
        (t, [Copia (t, ConstString n)])

    | ExpChar (n, Char) ->
        let t = novo_temp () in
        (t, [Copia (t, ConstChar n)])

    | ExpOp (op, exp1, exp2) ->
        (* Para expressões binárias, primeiro, se traduzem as expressões da       *)
        (* esquerda e da direita para seus respectivos equivalentes em código de  *)
        (* 3 endereçõs para depois traduzir a expressão inteira.                  *)
        let (endr1, codigo1) = let (e1,t1) = exp1 in traduz_exp e1
        and (endr2, codigo2) = let (e2,t2) = exp2 in traduz_exp e2
        and t = novo_temp () in
        let codigo = codigo1 @ codigo2 @ [AtribBin (t, endr1, op, endr2)] in
        (t, codigo)

    | ExpUn (op, exp1) ->
        (* Análogo as expressões binárias, porém aqui há apenas um operando após  *)
        (* o operador.                                                            *)
        let (endr1, codigo1) = let (e1,t1) = exp1 in traduz_exp e1
        and t = novo_temp () in
        let codigo = codigo1 @ [AtribUn (t, op, endr1)] in
        (t, codigo)

    | ExpFun (id,args,tipo_fn) ->
        let (enderecos, codigos) = List.split (List.map traduz_exp args) in
        let tipos = List.map pega_tipo args in
        let endr_tipos = List.combine enderecos tipos
        and t = novo_temp () in
        let codigo = (List.concat codigos) @ [CallFn (t, id, endr_tipos, tipo_fn)]
        in
        (t, codigo)

    | _ -> failwith "traduz_exp: nao implementado."


(* Traduz os comandos da mini linguagem em seus respectivos equivalentes em       *)
(* código de 3 endereços.                                                         *)
let rec traduz_cmd cmd =
    match cmd with
    (* Traduzindo os comandos de atribuição da mini linguagem *)
    | CmdAtrib (elem,ExpInt (n,Int)) ->
        let (endr_elem, codigo_elem) = traduz_exp elem 
        in codigo_elem @ [Copia (endr_elem, ConstInt n)]

    | CmdAtrib (elem,ExpFloat (n,Float)) ->
        let (endr_elem, codigo_elem) = traduz_exp elem 
        in codigo_elem @ [Copia (endr_elem, ConstFloat n)]

    | CmdAtrib (elem,ExpBool (n,Bool)) ->
        let (endr_elem, codigo_elem) = traduz_exp elem 
        in codigo_elem @ [Copia (endr_elem, ConstBool n)]

    | CmdAtrib (elem,ExpString (n,String)) ->
        let (endr_elem, codigo_elem) = traduz_exp elem 
        in codigo_elem @ [Copia (endr_elem, ConstString n)]

    | CmdAtrib (elem, ExpChar (n,Char)) ->
        let (endr_elem, codigo_elem) = traduz_exp elem 
        in codigo_elem @ [Copia (endr_elem, ConstChar n)]

    | CmdAtrib (elem,exp) ->
        let (endr_exp, codigo_exp) = traduz_exp exp 
        and (endr_elem, codigo_elem) = traduz_exp elem in
        let codigo = codigo_exp @ codigo_elem @ [Copia (endr_elem, endr_exp)] in
        codigo

    (* Traduzindo os comandos de leitura da mini linguagem. *)
    | CmdReadInt (elem) ->
        let (endr_elem, codigo_elem) = traduz_exp elem
        and t = novo_temp ()
        in
        [CallFn (t, "read_int", [], Int)] @ codigo_elem @ [Copia (endr_elem, t)]

    | CmdReadFloat (elem) ->
        let (endr_elem, codigo_elem) = traduz_exp elem
        and t = novo_temp ()
        in
        [CallFn (t, "read_float", [], Float)] @ codigo_elem @ [Copia (endr_elem, t)]

    | CmdReadString (elem) ->
        let (endr_elem, codigo_elem) = traduz_exp elem
        and t = novo_temp ()
        in
        [CallFn (t, "read_string", [], String)] @ codigo_elem @ [Copia (endr_elem, t)]

    | CmdReadChar (elem) ->
        let (endr_elem, codigo_elem) = traduz_exp elem
        and t = novo_temp ()
        in
        [CallFn (t, "read_char", [], Char)] @ codigo_elem @ [Copia (endr_elem, t)]

    | CmdWhile (teste,corpo) ->
        let (endr_teste, codigo_teste) = traduz_exp teste
        and codigo_verdadeiro = traduz_cmds corpo
        and rotulo_comeco = novo_rotulo "L"
        and rotulo_falso = novo_rotulo "L" in
        [rotulo_comeco] @ codigo_teste  @ [IfFalse (endr_teste, rotulo_falso)] @ codigo_verdadeiro @ [Goto rotulo_comeco] @
        [rotulo_falso]
        
    | CmdFor (inicio,teste,fim,corpo) ->
        let codigo_inicio = traduz_cmd inicio in
        (* Para não dar trabalho, vou converter o "for" em um comando "while" *)
        codigo_inicio @ traduz_cmd (CmdWhile (teste, corpo @ [fim]))

    | CmdIf (teste, entao, senao) ->
        let (endr_teste, codigo_teste) = traduz_exp teste 
        and codigo_entao = traduz_cmds entao 
        and rotulo_falso = novo_rotulo "L" in
       (match senao with
        | None ->
            codigo_teste @
            [IfFalse (endr_teste, rotulo_falso)] @
            codigo_entao @ 
            [rotulo_falso]
        | Some cmds -> 
            let codigo_senao = traduz_cmds cmds 
            and rotulo_fim = novo_rotulo "L" in
            codigo_teste @ 
            [IfFalse (endr_teste, rotulo_falso)] @
            codigo_entao @ 
            [Goto rotulo_fim] @
            [rotulo_falso] @ codigo_senao @
            [rotulo_fim])

    | CmdPrint args -> 
        let (enderecos, codigos) = List.split (List.map traduz_exp args) in
        let tipos = List.map pega_tipo args in
        let endr_tipos = List.combine enderecos tipos in
        (List.concat codigos) @
        [Call ("print", endr_tipos, Void)]

    | CmdReturn exp ->
       (match exp with
        | None -> [Return None]
        | Some e ->
            let (endr_exp, codigo_exp) = traduz_exp e in
            codigo_exp @ [Return (Some endr_exp)])

    | CmdSwitch (var,cases,default) ->
        traduz_cmd (converte_if var cases default)

    | CmdFun (ExpFun (id, args, tipo_fn)) -> 
        let (enderecos, codigos) = List.split (List.map traduz_exp args) in
        let tipos = List.map pega_tipo args in
        let endr_tipos = List.combine enderecos tipos in
        (List.concat codigos) @
        [Call (id, endr_tipos, tipo_fn)]

    | _ -> failwith "traduz_cmd: nao implementado"


and traduz_cmds cmds =
  match cmds with
  | [] -> []
  | cmd :: cmds ->
     let codigo = traduz_cmd cmd in
     codigo @ traduz_cmds cmds

let traduz_fun ast =
  let trad_local x =
    match x with
      DecVar ((id,pos),t) -> Local (id,t)
  in
  match ast with
    DecFun {fn_nome; fn_tiporet; fn_formais; fn_locais; fn_corpo} ->  
    let nome = fst fn_nome
    and formais = List.map (fun ((id,pos),tipo) -> Recebe (id,tipo)) fn_formais
    and nformais = List.length fn_formais
    and locais = List.map trad_local fn_locais
    and nlocais = List.length fn_locais 
    and corpo = traduz_cmds fn_corpo 
    in
    [BeginFun (nome,nformais,nlocais)] @ formais @ locais @ corpo @ [EndFun]
        

let tradutor ast_tipada =
  let trad_global x =
    match x with
      DecVar ((id,pos),t) -> Global (id,t)
  in
  let _ = zera_contadores () in 
  let (Programa (decs_globais, decs_funs, corpo)) = ast_tipada in
  let globais_trad = List.map trad_global decs_globais in
  let funs_trad = List.map traduz_fun decs_funs in
  let corpo_trad = traduz_cmds corpo in
  globais_trad @ (List.concat funs_trad) @ 
  [BeginFun ("main",0,0)] @ corpo_trad @ [EndFun]































