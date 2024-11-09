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

            #|/div:docs|#))

  (script "initialize();")))
