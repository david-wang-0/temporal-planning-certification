signature LIST_UTILS =
sig
    val zip_with_index : 'a list -> ('a * int) list
    val sort_by_index : 'a list -> ('a -> int) -> 'a list
    val pair_list_to_fun: (''a * 'b) list -> 'b -> ''a -> 'b
end


structure ListUtils : LIST_UTILS =
struct

    fun zip_with_index xs = 
        ListPair.zip (xs, List.tabulate (List.length xs, (fn i => i)))

    fun sort_by_index xs f =
        ListPair.zip (xs, (map f xs))
        |> ListMergeSort.sort (fn (x, y) => (snd x > snd y)) 
        |> List.map fst

    fun pair_list_to_fun xs default = (fn x =>
        (List.find (fn (a, b) => a = x) xs)
        |> Option.map snd
        |> (the_default default)
    )

end