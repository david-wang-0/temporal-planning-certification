(* signature COMPARABLE =
sig
    val comp : 'a -> 'a -> order
end

fun merge xs ys acc =
    (case (xs, ys) of 
        ([], ys) => List.revAppend(acc, ys) |
        (xs, []) => List.revAppend(acc, xs) |
        (x::xs, y::ys) => (
            if (x <= y) then 
        )
    )

fun sort l xs acc =
    let 
        val merge = (fn ls => (case ls of 
            ([], ys) => ys |
            (xs, []) => xs |
            (x::xs, y::ys) => (
                if (x <= y) then 
            )
        ))
    in (case (l, xs) of
        (0, xs) => xs |
        (1, xs) => xs |
        (l, xs) => 
    ) end *)

fun sort_by_index xs f =
    ListPair.zip xs (map f xs)
    |> ListMergeSort.sort (fn (x, y) => (snd x > snd y)) 
    |> List.map fst