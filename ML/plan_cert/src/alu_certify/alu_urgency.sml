(* Urgency repair for the MLunta successor relation (UNTRUSTED aLU checker support).

   MLunta's own urgent-location encoding is VACUOUS: rewrite_bexps compiles an urgent
   location to the invariant `"0" <= 0` plus a `Reset ("0", 0)` on every edge -- both
   DBM no-ops on the zero-reference clock -- so `#trans` happily lets time pass in urgent
   locations.  tck-reach (the oracle) handles `urgent:` natively, so without repair even
   inclusion-closed covreach certificates fail the invariant check (observed on
   MatchCellar 2: a delayed successor out of an urgent location that tck never explores).

   Repair (Munta's own approach, cf. its synthetic `_urge` clock appended LAST in
   make_renaming): transform the PARSED muntax network before construction --

     - append a real clock `_urge` at the END of the clock list (so the model DBM
       dimension becomes cert-dim + 1, with `_urge` at the last index);
     - reset `_urge := 0` on every edge whose TARGET is urgent;
     - conjoin invariant `_urge <= 0` onto every urgent location.

   Then delay at an urgent location is genuinely blocked by up-then-invariant.  Only the
   aLU checker's OWN parse sees this augmented model; the oracle pipeline (muntax file,
   renaming, tck) is untouched, and the certificate's DBMs are padded with an
   unconstrained `_urge` row/column at load time (alu_certify.close_zone) -- a sound
   over-approximation, since the true reachable states always have `_urge = 0` when it
   matters (it is reset on entry to every urgent location). *)

structure AluUrgency =
struct

  val urge = "_urge"

  fun aug_node urgent ({id, name, invariant} : ParseBexpTypes.node) : ParseBexpTypes.node =
    {id = id, name = name,
     invariant =
       if List.exists (fn x => x = id) urgent
       then Syntax.Invariant.And
              (Syntax.Invariant.Constr (Syntax.Constraint.Le (urge, 0)), invariant)
       else invariant}

  fun aug_edge urgent ({source, target, guard, label, update} : ParseBexpTypes.edge)
      : ParseBexpTypes.edge =
    {source = source, target = target, guard = guard, label = label,
     update =
       if List.exists (fn x => x = target) urgent
       then Syntax.Reset (urge, 0) :: update
       else update}

  fun aug_automaton (name, {nodes, edges, initial, committed, urgent}
                           : ParseBexpTypes.automaton) =
    (name,
     {nodes = List.map (aug_node urgent) nodes,
      edges = List.map (aug_edge urgent) edges,
      initial = initial, committed = committed, urgent = urgent}
     : ParseBexpTypes.automaton)

  fun add_urge ({automata, clocks, vars, formula, broadcast_channels}
                : ParseBexpTypes.network) : ParseBexpTypes.network =
    {automata = List.map aug_automaton automata,
     clocks = clocks @ [urge],
     vars = vars, formula = formula, broadcast_channels = broadcast_channels}

  (* muntax JSON -> _urge-augmented parsed network (pre-construction) *)
  fun parse_augmented (muntax_str : string) =
    muntax_str
    |> Parser.parse
    |> Either.mapR add_urge

end
