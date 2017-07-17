//$(document).ready(function(){
$(document).on( 'mousemove', '.type, .cat', function(){
    $(".type, .cat").hover(
    		function(){
        $(this).closest(".ttterm, .leaf, .unary, .binary").addClass("highlight");
        }, function(){
        $(this).closest(".ttterm, .leaf, .unary, .binary").removeClass("highlight");
    });
});

/*
$(document).ajaxComplete(function() {
    jQuery('.tabs .tab-links a').on('click', function(e)  {
    var currentAttrValue = jQuery(this).attr('href');
        // Show/Hide Tabs
        jQuery('.tabs ' + currentAttrValue).fadeIn(400).siblings().hide();
        // Change/remove current tab to active
        jQuery(this).parent('li').addClass('active').siblings().removeClass('active');
        e.preventDefault();
    });
});
*/

/*
jQuery(document).ready(function() {
  iframe = document.getElementById('fracas_problems');
  iframedoc = iframe.contentDocument || iframe.contentWindow.document;
  iframedoc.body.innerHTML = 'Hello world';
  alert{'ddd'};
});
*/

/*
$( document ).ready(function() {
    alert( "ready!" );
});
*/

