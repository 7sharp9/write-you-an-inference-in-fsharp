[<AutoOpenAttribute>]
module List
    let (++) = List.append

    let rec deleteByEq xs x =
        match xs with
        | [] -> []
        | ( y :: ys) ->
            if x = y then ys else y :: deleteByEq ys x

    let difference xs1 xs2=
        List.fold deleteByEq xs1 xs2