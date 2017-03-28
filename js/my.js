function toggle_block(idd) {
     var elem=document.getElementById(idd);
     var hide = elem.style.display =="none";
     if (hide) {
         elem.style.display="block";
    } 
    else {
      	 elem.style.display="none";
    }
}


function show_proof_tree() {
	var ent = document.getElementById("entailment_tableau");
	var cont = document.getElementById("contradiction_tableau");
    var val = document.getElementById("select_proof").value;
	if ( val == "Entailment") {
		ent.style.display="block";
		cont.style.display="none";
	} else {
		cont.style.display="block";
		ent.style.display="none";
	} 
}


// for autoexapnd of textarea
$(document)
		.one('focus.textarea', '.autoExpand', function(){
			var savedValue = this.value;
			this.value = '';
			this.baseScrollHeight = this.scrollHeight;
			this.value = savedValue;
		})
		.on('input.textarea', '.autoExpand', function(){
			var minRows = this.getAttribute('data-min-rows')|0,
				 rows;
			this.rows = minRows;
        console.log(this.scrollHeight , this.baseScrollHeight);
			rows = Math.ceil((this.scrollHeight - this.baseScrollHeight) / 17);
			this.rows = minRows + rows;
		});

$(document)
		.one('focus.textarea', '#message_text', function(){
			var savedValue = this.value;
			this.value = '';
			this.baseScrollHeight = this.scrollHeight;
			this.value = savedValue;
		})
		.on('input.textarea', '#message_text', function(){
			var minRows = this.getAttribute('data-min-rows')|0,
				 rows;
			this.rows = minRows;
        console.log(this.scrollHeight , this.baseScrollHeight);
			rows = Math.ceil((this.scrollHeight - this.baseScrollHeight) / 17);
			this.rows = minRows + rows;
		});


// tabs functionality
//jQuery(document).ready(function() {
    //jQuery('.tabs .tab-links a').on('click', function(e)  {  
$(document).on('click', '.tabs .tab-links a', function(e){    
        var currentAttrValue = jQuery(this).attr('href');
        // Show/Hide Tabs
        jQuery('.tabs ' + currentAttrValue).fadeIn(400).siblings().hide();
        // Change/remove current tab to active
        jQuery(this).parent('li').addClass('active').siblings().removeClass('active');
        //$('#data_type').val('1').trigger('change');
        $('#data_type').val(currentAttrValue.slice(1)).change();
        //jQuery('#data_type[value=sick]').prop('selected',true);
        //$('#data_type').removeAttr('selected').filter('[value=sick]').attr('selected', true);
        e.preventDefault();
    });
//});


/*$('.id_100 option')
     .removeAttr('selected')
     .filter('[value=val1]')
         .attr('selected', true)
*/

$(document).on('click', 'i.fa.fa-plus-square-o, i.fa.fa-minus-square-o', function(e){
    jQuery(this).parent('.id_sent').siblings().slideToggle(200);
    if (jQuery(this).is('.fa-minus-square-o')) {
        jQuery(this).addClass('fa-plus-square-o');
        jQuery(this).removeClass('fa-minus-square-o');
    } else {
        jQuery(this).addClass('fa-minus-square-o');
        jQuery(this).removeClass('fa-plus-square-o');
    }
});







