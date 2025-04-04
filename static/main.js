// ============================================================

var config = null;
var last_err_start = null;
var last_err_end = null;

/* Compiled templates, represented as functions that take objects
 * and produce HTML strings. Initialized by initialize.
 */
// let template_x = null;

/* Initialize the page: compile templates, set game-changing callback, and load
 * the game configurations from the server.
 */
function initialize() {
    // template_x = Handlebars.compile($('#template_x').html());
    ajax_json({
        url: "config.json",
        method: "GET",
        success: function(resp) {
            config = resp;
            $.each(config.fill, function(index, obj) {
                let option = $("<option>");
                option.text(obj.name);
                $("#loader").append(option);
            });
        },
        error: function() { }
    });

    $("#prooftext").on("change", (event) => prooftext_changed());
    $("#prooftext").on("input", (event) => prooftext_changed());

    $("#checkproof").on("click", (event) => check_prooftext());
    $("#loader").on("input", (event) => select_prooftext());
    $("#load").on("click", (event) => load_prooftext());
    $("#selecterr").on("click", (event) => select_last_error());
}

/* If the proof text has changed, mark the output as outdated.
 */
function prooftext_changed() {
    clear_feedback(false, false);
}

function select_prooftext() {
    let index = $("#loader").prop("selectedIndex");
    if (index > 0) {
        $("#load").attr("disabled", false);
    } else {
        $("#load").attr("disabled", true);
    }
}

function load_prooftext() {
    let index = $("#loader").prop("selectedIndex");
    if (index > 0) {
        let fill = config.fill[index-1];
        let program = "";
        $.each(fill.lines, function(index, line) {
            program = program + line + "\n";
        });
        $("#prooftext").prop("value", program);
        clear_feedback(true, true);
    }
}

function clear_feedback(hideLastResult, upToDate) {
    $("#load_nothing").prop("selected", true);
    $("#load").attr("disabled", true);
    $("#selecterr_area").hide();
    if (hideLastResult) {
        $("#output_outer_area").hide();
    }
    if (upToDate) {
        $("#out_of_date").hide();
    } else {
        $("#out_of_date").show();
    }
}

function select_last_error() {
    let prooftext = document.getElementById("prooftext");
    prooftext.focus();
    prooftext.setSelectionRange(last_err_start, last_err_end);
}

/* Submit the prooftext for checking, then update the output display.
 */
function check_prooftext() {
    clear_feedback(true, true);
    $("#wait_for_server").show();
    ajax_json({
        url: config.check_url || "check",
        method: "POST",
        data: { proof: $("#prooftext").val() },
        success: function(resp) {
            let area = $("#output_area");
            let inner = $("#output_inner_area");
            if (resp.error) {
                area.removeClass("check_good");
                area.addClass("check_bad");
            } else {
                area.removeClass("check_bad");
                area.addClass("check_good");
            }
            if (resp.format == "html") {
                inner.html($(resp.errorh || resp.passh));
            } else if (resp.format == "text") {
                let pre = $("<pre>");
                pre.html(resp.error || resp.pass);
                inner.html(pre);
            }
            if (resp.end) {
                last_err_start = resp.start;
                last_err_end = resp.end;
                $("#selecterr_area").show();
            } else {
                last_err_start = null;
                last_err_end = null;
                $("#selecterr_area").hide();
            }
            $("#output_outer_area").show();
            $("#wait_for_server").hide();
            $("#prooftext").focus();
        },
        error: function() {
            $("#output_area").removeClass("check_good");
            $("#output_area").addClass("check_bad");
            $("#output_inner_area").html("<p>The server raised an exception.</p>");
            $("#output_outer_area").show();
            $("#wait_for_server").hide();
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

