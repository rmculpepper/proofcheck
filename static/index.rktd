(html
 (head (title "Proof Checker")

       (meta ([charset "utf-8"]))
       (link ([href "main.css"]
              [rel "stylesheet"]
              [type "text/css"]))

       #;
       ;; Handlebars via CDN ( https://cdnjs.com/libraries/handlebars.js )
       (script ([src "https://cdnjs.cloudflare.com/ajax/libs/handlebars.js/4.7.8/handlebars.min.js"]
                [integrity "sha512-E1dSFxg+wsfJ4HKjutk/WaCzK7S2wv1POn1RRPGh8ZK+ag9l244Vqxji3r6wgz9YBf6+vhQEYJZpSjqWFPg9gg=="]
                [crossorigin "anonymous"]
                [referrerpolicy "no-referrer"]))

       ;; jQuery via CDN ( https://releases.jquery.com/ )
       (script ([src "https://code.jquery.com/jquery-3.7.1.min.js"]
                [integrity "sha256-/JqT3SQfawRcv/BIHPThkBvs0OEvtFFmqPF/lYI/Cxo="]
                [crossorigin "anonymous"]))

       (script ([src "main.js"]
                [type "text/javascript"]))

       #|/head|#)

 (body

  (div ([class "main_area"])
       (h1 "Proof Checker")

       (div ([id "proof_area"])
            (h2 "Proof")

            (div () (label ([for "prooftext"]) "Proof"))
            (div ()
                 (textarea ([id "prooftext"]
                            [rows "20"]
                            [cols "80"]
                            [maxlength "100000"]
                            [spellcheck "false"]
                            [placeholder "Enter your proof here."])))
            (div ()
                 (button ([id "checkproof"] [type "button"])
                         "Check proof")))

       (div ([id "output_area"] [style "display: none"])
            (h2 "Output")

            (p ([id "out_of_date"] [style "display: none"])
               "The proof has changed since it was last checked, "
               "so this output is out of date.")

            (div ([id "output_inner_area"]))

            #|/div:output|#)

       (div ([id "docs_area"])
            (h2 "Documentation")

            (p "The proof checker supports the following symbols and reserved words. "
               "Reserved words and identifiers are " (em "case sensitive") ".")

            (div (em "Logic and Arithmetic: ")
                 (pre "¬ not ∧ and ∨ or ⇒ implies ⇔ iff ∀ forall ∃ exists "
                      "∈ in ℕ NN"
                      "+ * ="))
            (div (em "Justifications: ")
                 (div (pre "∧Intro ∧ElimL ∧ElimR AndIntro AndElimL AndElimR"))
                 (div (pre "∨IntroL ∨IntroR ∨Elim OrIntroL OrIntroR OrElim"))
                 (div (pre "⇒Elim ⇒Intro ImpliesElim ImpliesIntro "
                      "ImplicationElim ImplicationIntro"))
                 (div (pre "⇔ElimF ⇔ElimB ⇔Intro IffElimF IffElimB IffIntro"))
                 (div (pre "∀Elim ∀Intro ForAllElim ForAllIntro"))
                 (div (pre "∃Elim ∃Intro ExistsElim ExistsIntro"))
                 (div (pre "↦ :->")))

            (p "The proof checker does not check membership of sets,"
               " such as for ∀Elim and ∃Intro.")
            (p "The proof checker does not yet support"
               " the 'by algebra' justification"
               " and the indirect proof rules.")

            (h3 "Example: Implication")

            (pre "
Axiom 1: Tue implies CS220
Axiom 2: Thu implies CS220
Axiom 3: CS220 implies Happy

1 Block
  1.1 Assume Tue
  1.2 Want Happy
  1.3 Derive CS220 by ImpliesElim on Axiom 1, #1.1
  1.4 Derive Happy by ImpliesElim on Axiom 3, #1.3
2 Derive Tue implies Happy by ImpliesIntro on #1
")

            (h3 "Example: Disjunction")

            (pre "
Axiom 1: sun implies (bike and garden)
Axiom 2: rain implies clean

1 Block
  1.1 Assume sun or rain
  1.2 Want garden or clean
  1.4 Block
    1.4.1 Assume sun
    1.4.2 Want garden or clean
    1.4.3 Derive bike and garden by ImpliesElim on Axiom 1, #1.4.1
    1.4.4 Derive garden by AndElimR on #1.4.3
    1.4.5 Derive garden or clean by OrIntroL on #1.4.4
  1.5 Derive sun implies (garden or clean) by ImpliesIntro on #1.4
  1.6 Block
    1.6.1 Assume rain
    1.6.2 Want garden or clean
    1.6.3 Derive clean by ImpliesElim on Axiom 2, #1.6.1
    1.6.4 Derive garden or clean by OrIntroR on #1.6.3
  1.7 Derive rain implies (garden or clean) by ImpliesIntro on #1.6
  1.8 Derive garden or clean by OrElim on #1.1, #1.5, #1.
2 Derive (sun or rain) implies (garden or clean) by ImpliesIntro on #1
")

            (h3 "Example: Universal")

            (pre "
Axiom 1: Small('Mouse')
Axiom 2: Brave('Lion')
Axiom 3: forall a,b in A, (Small(a) and Brave(b)) implies Fears(a,b)

1 Derive Small('Mouse') and Brave('Lion')
  by AndIntro on Axiom 1, Axiom 2
2 Derive (Small('Mouse') and Brave('Lion')) implies Fears('Mouse', 'Lion')
  by ForAllElim on Axiom 3 with a,b :-> 'Mouse', 'Lion'
3 Derive Fears('Mouse', 'Lion')
  by ImpliesElim on #2, #1
")
            #|/div:docs|#))

  (script "initialize();")))
