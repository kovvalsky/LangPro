<?xml version="1.0" encoding="UTF-8"?>
<!-- Transforms CCG trees and TT-terms into HTML -->
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">
    <xsl:output method="html" encoding="utf-8" doctype-system="about:legacy-compat"/>
    <xsl:template match="/">
        <html>
            <head>
                <!-- 
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.0/jquery.min.js">//</script>
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jqueryui/1.9.2/jquery-ui.min.js">//</script>
                <script type="text/javascript" src="PATH_TO/jquery.jsPlumb-1.5.4-min.js ">//</script>
                -->
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.0/jquery.min.js"></script>
                <script type="text/javascript" src="../js/myfunctions.js"></script>
                <script type="text/javascript" src="../js/my.js"></script>
                <link rel="stylesheet" type="text/css" href="../css/ttterms.css"/>
                <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.6.3/css/font-awesome.min.css"/>
                <title>TTterms</title>
            </head>
            <body style="text-align:center;">
                <xsl:apply-templates/>
            </body>
        </html>
    </xsl:template>

    <!-- ####################### LIST OF TEMPLATES ####################### -->

    <xsl:template match="parsed_problem">
        <div class="parsed_problem">
            <div class="parsed_problem_title">
				<xsl:text>Problem </xsl:text>
				<xsl:value-of select="./@probID" />
                <xsl:text>: For each sentence, CCG derivation > CCG term > corrected CCG term > the first LLF</xsl:text>
            </div>
            <xsl:apply-templates/>
        </div>
    </xsl:template>
    
    <xsl:template match="parsed_sentence">
        <div class="parsed_sentence">
            <xsl:apply-templates/>
        </div>
    </xsl:template> 
    
    <xsl:template match="id_sent">
        <div class="id_sent">
            <i class="fa fa-minus-square-o"></i>
            <xsl:copy-of select="."/>
        </div>
    </xsl:template>


<!-- TTTerms -->
    <xsl:template match="ccgterm|ccgtree|corr_ccgterm|llf">
        <div class="fullttterm"> <!--style="display:none;">-->
            <xsl:apply-templates/>
        </div>
    </xsl:template>

    <xsl:template match="ttterm">
        <span class="ttterm">
            <div class="ttexp">
                <xsl:apply-templates select="var|tlp|app|abst|ttterm"/>
            </div>
            <div class="type">
                <xsl:copy-of select="type"/>
            </div>
        </span>
    </xsl:template>

    <xsl:template match="tlp|leaf">
        <span class="{name(.)}">
            <div class="lem">
                <xsl:value-of select="lem"/>
            </div>
            <div class="tok">
                 <xsl:value-of select="tok"/>
            </div>
            <div class="pos">
                <xsl:value-of select="pos"/>
            </div>
            <div class="ner">
                <xsl:value-of select="ner"/>
            </div>
            <xsl:apply-templates select="cat"/>
        </span>
    </xsl:template>

    <xsl:template match="var">
        <span class="var">
            <xsl:value-of select="."/>
        </span>
    </xsl:template>

    <xsl:template match="app">
        <span class="app">
            <xsl:apply-templates select="ttterm[1]"/>
            <xsl:apply-templates select="ttterm[2]"/>
        </span>
    </xsl:template>

    <xsl:template match="abst">
        <span class="abst">
            <span class="lambda">
                <xsl:text>&#955;</xsl:text>
            </span>
            <span class="ttterm">
                <div class="ttexp">
                    <span class="var">
                        <xsl:value-of select="ttterm[1]/var"/>
                        <xsl:text>.</xsl:text>
                    </span>
                </div>
                <div class="type">
                    <xsl:copy-of select="ttterm[1]/type"/>
                </div>
            </span>
            <xsl:apply-templates select="ttterm[2]"/>
        </span>    
    </xsl:template>
<!-- TTTerms -->


<!-- CCG tree -->
    <xsl:template match="binary">
        <span class="binary">
            <xsl:apply-templates select="leaf|unary|binary|rule"/>     
            <xsl:apply-templates select="cat"/>
        </span>
    </xsl:template>
    
    <xsl:template match="unary">
        <span class="unary">
            <xsl:apply-templates select="leaf|unary|binary|rule"/>
            <xsl:apply-templates select="cat"/>
        </span>
    </xsl:template>
   
    <xsl:template match="cat">
        <div class="cat"><xsl:copy-of select="."/></div>
    </xsl:template>
    
    <xsl:template match="rule">
        <div class="rule"><span><xsl:copy-of select="."/></span></div>
    </xsl:template>
    
<!-- CCG tree -->

</xsl:stylesheet>

