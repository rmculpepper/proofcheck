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

       (p ([class "warning"])
          "Make sure to save your work often to an external editor. " (br)
          "Reloading this page may clear the proof text.")

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
                         "Check proof")
                 (button ([id "selecterr"] [type "button"] [disabled "disabled"])
                         "Select error")))

       (div ([id "output_area"] [style "display: none"])
            (h2 "Output")

            (div ([id "wait_for_server"] [class "waiting"] [style "display: none"])
                 (div ([class "par"]) "Waiting for the server to respond."))

            (div ([id "out_of_date"] [class "outdated"] [style "display: none"])
                 (div ([class "par"])
                      "The proof has changed since it was last checked, " (br)
                      "so this output may be out of date."))

            (div ([id "output_inner_area"]))

            #|/div:output|#)

       (div ([id "docs_area"])
            (h2 "Documentation")

            (p "The proof checker supports the following symbols and reserved words. "
               "Reserved words and identifiers are " (em "case sensitive") ".")

            (div (em "Logic and Arithmetic: ")
                 (div (pre "not and or implies iff forall exists ¬ ∧ ∨ ⇒ ⇔ ∀ ∃ "))
                 (div (pre "+ * = in ∈ NN ℕ ")))
            (div (em "Rule names: ")
                 (div (pre "AndIntro AndElimL AndElimR ∧Intro ∧ElimL ∧ElimR "))
                 (div (pre "OrIntroL OrIntroR OrElim ∨IntroL ∨IntroR ∨Elim "))
                 (div (pre "ImpliesElim ImpliesIntro ⇒Elim ⇒Intro "))
                 (div (pre "IffElimF IffElimB IffIntro ⇔ElimF ⇔ElimB ⇔Intro "))
                 (div (pre "ForAllElim ForAllIntro ∀Elim ∀Intro "))
                 (div (pre "ExistsElim ExistsIntro ∃Elim ∃Intro "))
                 (div (pre "ModusTollens DisjunctiveSyllogism Contradiction"))
                 (div (pre "Algebra Repeat")))
            (div (em "Justifications: ")
                 (div (pre "by on with := ↦ forward backward")))

            #|/div:docs_area|#)

       (div
        (a ([href "mini.html"]
            [onclick "event.preventDefault(); window.open('mini.html', '_blank', 'popup');"])
           "Minimal Version"))))
  (script "initialize();")))
