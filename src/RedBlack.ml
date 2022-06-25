(* Red-black trees according to the following papers :

   Chris Okasaki, Red-Black Trees in a Functional
   Setting. J. Funct. Program. 9(4): 471-477 (1999)

   Adaptation of :
   Kimball Germane and Matthiew Might, Deletion : The curse of the Red-Black Tree
   Setting. J. Funct. Program. 24 (4): 423–433, 2014.
   To work with a red black tree

*)

type colour = Red | Black

type 'a t = L | T of colour * 'a t * 'a * 'a t

let empty = L

(* utility function *)
let is_empty m = (m = empty)

let blacken = function
    L  -> L
  | T (_, left, root, right) -> T (Black, left, root, right)

let redden = function
    L  -> failwith "can't redden leaf"
  | T (_, left, root, right) -> T (Red, left, root, right)

let rec pp f ppf = function
    L   -> Format.fprintf ppf "Leaf"
  | T (c, l, root, r) ->
    Format.fprintf ppf "Tree (%s,%a,%a,%a)"
      (match c with  Red -> "Red" | Black -> "Black")
      (pp f) l
      f root
      (pp f) r

let max t =
  let rec max opt = function
    | L -> opt
    | T (_,_,x,l) -> max (Some x) l
  in max None t

let count tree =
  let rec aux count = function
    | L -> count
    | T (_, l,_,r) -> aux (aux (count + 1) l) r
  in aux 0 tree

let blackDepth tree =
  let rec aux count = function
    | L -> count + 1
    | T (Red        , l, _, _) -> aux count l
    | T (Black      , l, _, _) -> aux (count + 1) l
  in aux 0 tree

exception Not_equal
let rec checkDepth = function
  | L -> 1
  | T (colour, l, _, r) ->
    let lcount = checkDepth l in
    let rcount = checkDepth r in
    if lcount <> rcount then raise Not_equal
    else match colour with
        Red         -> lcount
      | Black       -> lcount + 1

let checkDepth_opt tree =
  try Some (checkDepth tree) with
    Not_equal -> None

(* Okasaki's balance function for insertion *)
let balance colour left(*n*) root right(*n*) =
  match colour, left, root, right with
    Black, T (Red, T (Red, a, x, b), y, c), z, d
  | Black, T (Red, a, x, T (Red, b, y, c)), z, d
  | Black, a, x, T (Red, T (Red, b, y, c), z, d)
  | Black, a, x, T (Red, b, y, T (Red, c, z, d)) ->
    T (Red, T (Black, a, x, b), y, T (Black, c, z, d)) (*n+1*)
  | _ ->
    T (colour, left, root, right) (*n+1 if color black*)


type choice = Old | New

let choose ~old ~new' = function
    Old -> old
  | New -> new'


(* Insertion from Okasaki *)
let insert ~cmp elt tree =
  let rec insert = function
      L -> T (Red, L, elt, L)  (* A leaf *)
    | T (colour, left, root, right) ->
      let diff = cmp elt root in
      if diff = 0 then
        T (colour, left, elt, right)
      else if diff < 0 then
        balance colour (insert left) root right
      else
        balance colour left root (insert right)
  in
  blacken (insert tree)


(* Adaptation of Might function *)
let delete : cmp:('a -> 'b -> int) -> 'a -> 'b t -> 'b t =
  fun ~cmp x tree ->
  let rec del = function
    | L -> raise Not_found
    | T (k, l, y ,r) as nod ->
      let c = cmp x y in
      if c < 0 then balance_left k (del l) y r
      else if c > 0 then balance_right k l y (del r)
      else remove nod

  and remove = function
    (* Remove a leaf *)
    | T (Red  , L, _, L) -> L, false
    | T (Black, L, _, L) -> L, true
    (* Only one child implies the child is red and the parent is black *)
    | T (Black, T (Red, l, v, r), _, L)
    | T (Black, L, _, T (Red, l, v, r)) -> T (Black, l, v, r), false
    (* Two sub-trees*)
    | T (c, l, _, r) ->
      let v = Option.get @@ max l in
      let l' = remove_max l in
      balance_left c l' v r
    | L -> failwith "impossible"

  and balance_left colour (left, is_shorter) value right =
    if is_shorter then
      match colour, left, value, right with
      (* case 1 : The sibling is red so the parent is black.
         fix : Perform a rotation. d needs to be turn red which may violate 1.
         but balance restore porperty 1. *)
      | Black, a, x, T (Red, T (Black, b, y, c), z, d)
        -> T (Black, T (Black, a, x, b), y, balance Black c z (redden d)),false
      (* case 2: The sibling is black and has at least a red child. Then he has at least three black children.
         fix : simple rotation, repaint in black.  *)
      | k, a, x, T (Black, T (Red, b, y, c), z, d)
      | k, a, x, T (Black, b, y, T (Red, c, z, d))
        -> T (k, T (Black, a, x, b), y, T (Black, c, z, d)),false
      (* case 3: The sibling is black with two black child.
         case 3.i the parent is red, turn the root black and the siblign red
         case 3.ii the parent is black, turn the siblign red and propagate that
         the subtree starting with the parent is shorter by one *)
      | k, x, y, T (Black, c, z, d)
        -> T (Black, x, y, T (Red, c, z, d)),k=Black
      | (Black, _, _, T (Red, T (Red, _, _, _), _, _)) | (Red, _, _, T (Red, _, _, _)) -> failwith "toto"
      | (Black, _, _, T (Red, L, _, _)) | (_, _, _, L) -> failwith "toto"
    else
      T(colour, left, value, right),false

  and balance_right colour left value (right,is_shorter) =
    (* complemaentary as the above *)
    if is_shorter then
      match colour, left, value, right with
      | Black, T (Red, a, x, T (Black, b, y, c)), z, d
        -> T (Black, balance Black (redden a) x b, y, T (Black, c, z, d)),false
      | k, T (Black, T (Red, a, x, b), y, c), z, d
      | k, T (Black, a, x, T (Red, b, y, c)), z, d
        -> T (k, T (Black, a, x, b), y, T (Black, c, z, d)),false
      | k, T (Black, a, x, b), y, z
        -> T (Black, T (Red, a, x, b), y, z),k=Black
      | _ -> failwith "Impossible cases"
    else
      T(colour, left, value, right),false

  and remove_max =
    function
      T (_,_,_,L) as n -> remove n
    | T (c,l,v,r) -> balance_right c l v @@ remove_max r
    | L -> failwith "impossible"

  in fst @@ del tree

let delete_opt ~cmp elt tree =
  try Some (delete ~cmp elt tree) with Not_found -> None

let rec find ~cmp elt = function
    L -> raise Not_found
  | T (_, left, root, right) ->
    let diff = cmp elt root in
    if diff = 0 then (root)
    else if diff < 0
    then (find ~cmp elt left)
    else (find ~cmp elt right)

let find_opt ~cmp elt tree =
  try Some (find ~cmp elt tree) with Not_found -> None

(* Inorder iterators *)

let rec iter f = function
    L -> ()
  | T (_, left, root, right) -> iter f left; f root; iter f right

let rec inorder acc = function
    L -> acc
  | T (_, left, root, right) -> inorder (root :: inorder acc right) left

let elements t = inorder [] t

let union ~cmp (tree_a : 'a t) tree_b =
  List.fold_left
    (fun acc elt -> insert ~cmp elt acc)
    tree_b
    (elements tree_a)

let rec fold_inc ~f ~init = function
    L -> init
  | T (_, left, root, right) ->
    fold_inc ~f ~init:(f root (fold_inc ~f ~init left)) right

let rec fold_dec ~f ~init = function
    L -> init
  | T (_, left, root, right) ->
    fold_dec ~f ~init:(f root (fold_dec ~f ~init right)) left
