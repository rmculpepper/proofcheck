(html
 (head (title "Proof Checker")
       (meta ([charset "utf-8"]))
       (link ([href "main.css"]
              [rel "stylesheet"]
              [type "text/css"]))
       ;; jQuery via CDN ( https://releases.jquery.com/ )
       (script ([src "https://code.jquery.com/jquery-3.7.1.min.js"]
                [integrity "sha256-/JqT3SQfawRcv/BIHPThkBvs0OEvtFFmqPF/lYI/Cxo="]
                [crossorigin "anonymous"]))
       (script ([src "main.js"]
                [type "text/javascript"]))
       #|/head|#)

 (body
  (div ([class "mini_main_area"])
       (div ([class "mini_loader_area"])
            (select ([id "loader"] [for "loader"])
                    (option ([id "load_nothing"] [selected "selected"])))
            (button ([id "load"] [type "button"] [disabled "disabled"]) "Load"))
       (h1 "Proof Checker")
       (div ([id "proof_area"])
            (div () (label ([for "prooftext"]) "Proof"))
            (div ()
                 (textarea ([id "prooftext"]
                            [rows "20"]
                            [cols "80"]
                            [maxlength "100000"]
                            [spellcheck "false"]
                            [placeholder "Enter your proof here."])))
            (div ()
                 (span
                  (button ([id "checkproof"] [type "button"])
                          "Check proof"))))

       (div ([id "output_outer_area"] [style "display: none"])
            (div ([id "wait_for_server"] [class "waiting"] [style "display: none"])
                 (div ([class "par"]) "Waiting for the server to respond."))
            (div ([id "out_of_date"] [class "outdated"] [style "display: none"])
                 (div ([class "par"])
                      "The proof has changed since it was last checked, " (br)
                      "so this output may be out of date."))
            (div ([id "output_area"])
                 (div ([id "output_inner_area"]))
                 (div ([id "selecterr_area"] [style "display: none"])
                      (button ([id "selecterr"] [type "button"])
                              "Select error location")))
            #|/div:output|#)
       (script "initialize();"))))
