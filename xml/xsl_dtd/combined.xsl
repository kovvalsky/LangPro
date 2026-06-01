<?xml version="1.0" encoding="UTF-8"?>

<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">

    <!-- Reuse the old stylesheets -->
    <xsl:import href="ttterms.xsl"/>
    <xsl:import href="tableau.xsl"/>

    <xsl:output method="html" encoding="utf-8" doctype-system="about:legacy-compat"/>

    <!-- New root template: produce ONE html document -->
    <xsl:template match="/">
        <html>
            <head>
                <!-- from ttterms.xsl -->
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.0/jquery.min.js"></script>
                <script type="text/javascript" src="../js/myfunctions.js"></script>
                <script type="text/javascript" src="../js/my.js"></script>

                <!-- both CSS files -->
                <link rel="stylesheet" type="text/css" href="../css/ttterms.css"/>
                <link rel="stylesheet" type="text/css" href="../css/tableau.css"/>

                <!-- shared icon font -->
                <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.6.3/css/font-awesome.min.css"/>

                <title>Parses and proof</title>
            </head>

            <body style="text-align:center;">
                <!-- first render parses.xml content -->
                <xsl:apply-templates select="/combined/parsed_problem"/>

                <!-- then render knowledge base content -->
                <xsl:apply-templates select="/combined/kb"/>


                <!-- then render proof-yes.xml content -->
                <xsl:apply-templates select="/combined/proof"/>
            </body>
        </html>
    </xsl:template>

    <!-- Override tableau.xsl's root-like tableau template.
         The original tableau.xsl creates a full <html> page.
         Here we only want the inner tableau block. -->
    <xsl:template match="tableau">
        <div class="tableau">
            <xsl:apply-templates/>
        </div>
    </xsl:template>

    <!-- Important conflict fix:
         both old stylesheets define a template for <llf>.
         In parses.xml, <llf> contains <ttterm>.
         In proof-yes.xml, <llf> is plain text inside <formula>. -->

    <!-- parsed LLF from parses.xml -->
    <xsl:template match="llf[ttterm]">
        <div class="fullttterm">
            <xsl:apply-templates/>
        </div>
    </xsl:template>

    <!-- proof/tableau LLF from proof-yes.xml -->
    <xsl:template match="formula/llf">
        <span class="llf">
            <xsl:value-of select="."/>
        </span>
    </xsl:template>


    <!-- new element, kb for knowledge base display -->
    <xsl:template match="kb">
        <div class="kb">
            <div class="kb_title">
                Knowledge Base
            </div>
            <div class="kb_content">
                <xsl:copy-of select="node()"/>
            </div>
        </div>
    </xsl:template>


    <xsl:template match="proof">
        <div class="proof" style="margin-top: 30px;">
            <xsl:apply-templates/>
        </div>
    </xsl:template>

    <!-- new element, title for a tableau that summarizes its status -->
    <xsl:template match="tableau_label">
        <div class="tableau_label">
            <span class="tableau_label_title">
                Tableau proof:
            </span>
            <span class="tableau_status">
            <xsl:value-of select="."/>
            </span>
        </div>
    </xsl:template>

</xsl:stylesheet>