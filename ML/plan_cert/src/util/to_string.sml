signature TO_STRING =
sig
    type t
    val to_string: t -> string
end

functor ListToString (
    structure Ty : TO_STRING
    val sep : string
    val start_delim : string
    val end_delim : string
) : TO_STRING = struct
    type t = Ty.t list

    fun intersperse y xs = 
    let 
        fun f (xs, acc) = (case xs of
            [] => List.rev acc |
            [x] => f ([], x::acc) |
            (x::xs) => f (xs, y::(x::acc))
        ) 
    in
        f (xs, [])
    end


    fun to_string (xs : t) =
        xs
        |> map (Ty.to_string)
        |> intersperse sep
        |> foldr (fn (x, y) => x ^ y) ""
        |> (fn xs => start_delim ^ xs ^ end_delim)
end

structure StringToString : TO_STRING = 
struct
    type t = string
    fun to_string s = s
end

structure IntToString : TO_STRING =
struct
    type t = Int.int
    fun to_string i = Int.toString i
end
