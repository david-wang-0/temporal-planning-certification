(* Standalone stub for Isabelle's `Term` structure.

   The unified Converter export (in Eval) emits the `typerep`/`heap` typeclass machinery for
   Munta's imperative DBM arrays as references to the real Isabelle `Term.typ` / `Term.Type`
   (e.g.  type 'a typerep = {typerep : 'a itself -> Term.typ};
          fun typerep_inta t = Term.Type ("Int.int", []); ...).
   The propositional-only export historically emitted these as a local `typerepa` datatype
   instead; the numeric additions pull in the `Term.`-qualified form.  `Term` is not part of a
   standalone SML program, so we provide the minimal datatype the generated code type-checks
   against.  These `typerep` functions are only ever stored in dictionaries, never invoked at
   runtime (no term reconstruction on the certification path), so the stub body is never run --
   it only needs to type-check.  Loaded before Check_Unsolvability.ML in converter.mlb so the
   `Term.*` references inside `structure Converter` resolve to it. *)
structure Term =
struct
  datatype typ = Type of string * typ list
end
