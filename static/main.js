// ============================================================

/* Compiled templates, represented as functions that take objects
 * and produce HTML strings. Initialized by initialize.
 */
// let template_x = null;

/* Initialize the page: compile templates, set game-changing callback, and load
 * the game configurations from the server.
 */
function initialize() {
    // template_x = Handlebars.compile($('#template_x').html());

    $("#prooftext").on("change", (event) => prooftext_changed());
    $("#prooftext").on("input", (event) => prooftext_changed());

    $("#checkproof").on("click", (event) => check_prooftext());
}

/* If the proof text has changed, mark the output as outdated.
 */
function prooftext_changed() {
    $("#out_of_date").show();
}

/* Submit the prooftext for checking, then update the output display.
 */
function check_prooftext() {
    ajax_json({
        url: "http://localhost:17180/check",
        method: "POST",
        data: { proof: $("#prooftext").val() },
        success: function(resp) {
            // resp.v resp.type (resp.error | resp.pass)
            if (resp.format == "text") {
                let pre = $("<pre>");
                pre.html(resp.error || resp.pass);
                $("#output_inner_area").html(pre);
            }
            $("#output_area").show();
            $("#out_of_date").hide();
        },
        error: function() {
            $("#output_area").show();
            $("#output_inner_area").html("<p>The server raised an exception.</p>");
            $("#out_of_date").hide();
        }
    });
}

// ============================================================
// Misc Utilities

/* Perform an AJAX request, sending JSON data and expecting a JSON response.
 */
function ajax_json(arg) {
    obj = {
        contentType : "application/json; charset=utf-8",
        processData : false,
        dataType : "json",
        cache : false
    };
    for (let key in arg) {
        switch (key) {
        case "data":
            obj.data = JSON.stringify(arg.data);
            break;
        default:
            obj[key] = arg[key];
            break;
        }
    }
    $.ajax(obj);
}

/* Compile a handlebars template embedded in the DOM within a script tag
 * identified by id.
 */
function handlebars_compile_id(id) {
    return Handlebars.compile(document.getElementById(id).innerHTML);
}

