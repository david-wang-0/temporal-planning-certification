signature ARRAY_UTILS =
sig
    val to_list : 'a array -> 'a list
end


structure ArrayUtils : ARRAY_UTILS =
struct

    fun to_list xs =
        Array.foldr (op ::) [] xs
end