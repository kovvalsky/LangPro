<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">
    <xsl:output method="html" encoding="utf-8" doctype-system="about:legacy-compat" />
    <xsl:template match="/">
        <html>
            <head>
                <!-- 
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.0/jquery.min.js">//</script>
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jqueryui/1.9.2/jquery-ui.min.js">//</script>
                <script type="text/javascript" src="PATH_TO/jquery.jsPlumb-1.5.4-min.js ">//</script>
                -->
                <link rel="stylesheet" type="text/css" href="tableau.css"></link>
                <title>Tableau</title>
            </head>
            <body style="text-align:center;">
                <xsl:apply-templates/>
            </body>
        </html>
    </xsl:template>
    
<!-- ####################### LIST OF TEMPLATES ####################### -->    
    
    <xsl:template match="premise">
        <div class="premise"><xsl:value-of select="."/></div>    
    </xsl:template>
    
    
    <xsl:template match="conclusion">
        <div class="conclusion">
            <xsl:text>? </xsl:text>
            <xsl:value-of select="."/>
        </div>    
    </xsl:template>
    
    
    <xsl:template match="tree">
        <xsl:if test="preceding-sibling::tree">
            <xsl:text>&#160;&#160;&#160;</xsl:text>
        </xsl:if>
        <table style="margin: auto;">        
        <xsl:choose>
            <xsl:when test="following-sibling::tree | preceding-sibling::tree">
                <xsl:attribute name="class">Branch</xsl:attribute>
            </xsl:when>
            <xsl:otherwise>
                <xsl:attribute name="class">nonBranch</xsl:attribute>
            </xsl:otherwise>
        </xsl:choose>
            <tr><xsl:apply-templates select="node"/></tr> 
            <tr><td><xsl:apply-templates select = "tree"/></td></tr>
        </table>    
    </xsl:template>
    
    
    <xsl:template match="node">
        <td>
		 	<xsl:choose>
        		<xsl:when test="child::closer[1]">
					<div class="closer_node">
					<xsl:value-of select="closer"/>
					</div>
		        </xsl:when>
        		<xsl:when test="child::model[1]">
					<div class="model">
					<xsl:value-of select="model"/>
					</div>
		        </xsl:when>
	        	<xsl:otherwise>
            		<xsl:if test="following-sibling::tree[2]">
                		<xsl:attribute name="class">parent2</xsl:attribute>
            		</xsl:if>
            		<div class="{formula/@sign}">
                		<div class="info">
                    		<xsl:value-of select="@id"/>
                    		<!-- <sup>(<xsl:value-of select="@id"/>)</sup> -->
                    		<xsl:apply-templates select="source"/>
                		</div>    
                		<xsl:apply-templates select="formula"/>
            		</div>
		        </xsl:otherwise>
			</xsl:choose>	
        </td>    
    </xsl:template>
    
    
    <xsl:template match="formula"> 
		<div class="llf"><xsl:apply-templates select="modList"/></div> 
        <div class="llf"><xsl:value-of select="llf"/></div>
        <div class="llf"><xsl:apply-templates select="argList"/></div>    
    </xsl:template>
    
    
    <xsl:template match="source">
        <xsl:text> : </xsl:text>
        <xsl:value-of select="@rule"/>
        <xsl:text>(</xsl:text>
        <xsl:apply-templates select="idList"/>
        <xsl:if test="oldConstList">
            <xsl:text>, </xsl:text>
            <xsl:apply-templates select="oldConstList"/>
        </xsl:if>   
        <xsl:text>)</xsl:text>
    </xsl:template>
    
    
    <xsl:template match="modList|argList|idList|oldConstList">
        <xsl:text>[</xsl:text>
        <xsl:for-each select="child::*[last()>position()]">
            <xsl:value-of select="."/>
            <xsl:text>, </xsl:text>
        </xsl:for-each>  
        <xsl:value-of select="child::*[last()]"/>
        <xsl:text>]</xsl:text>
    </xsl:template>
    
</xsl:stylesheet>
