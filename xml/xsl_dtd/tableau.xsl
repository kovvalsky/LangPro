<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" version="1.0">
    <xsl:output method="html" encoding="utf-8" doctype-system="about:legacy-compat" />
    <xsl:template match="tableau">
        <html>
            <head>
                <!-- 
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jquery/1.9.0/jquery.min.js">//</script>
                <script type="text/javascript" src="http://ajax.googleapis.com/ajax/libs/jqueryui/1.9.2/jquery-ui.min.js">//</script>
                <script type="text/javascript" src="PATH_TO/jquery.jsPlumb-1.5.4-min.js ">//</script>
                -->
                <link rel="stylesheet" type="text/css" href="../css/tableau.css"></link>
				<link rel="stylesheet" type="text/css" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/4.6.3/css/font-awesome.min.css"></link>
                <title>Tableau</title>
            </head>
            <body>
                <div class="tableau">
                    <xsl:apply-templates/>
                </div>   
            </body>
        </html>
    </xsl:template>
    
<!-- ###################### LIST OF TEMPLATES ####################### -->  
    
    <xsl:template match="problem">
        <div class="problem">
            <xsl:apply-templates/> 
        </div>            
    </xsl:template>
    
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
        <span class="tree">    
            <xsl:apply-templates select="node|subTrees"/>
        </span>    
    </xsl:template>
    
    <xsl:template match="subTrees">  
        <div class="subTrees">    
            <xsl:apply-templates/>
        </div>    
    </xsl:template> 
    
    <xsl:template match="node">  
        <div class="node">    
            <!--<xsl:attribute name="absID">
                <xsl:value-of select="@absId"/>
            </xsl:attribute>-->
            <xsl:if test="@id">
            <span class="node_id"><xsl:value-of select="@id"/></span>
            </xsl:if>    
            <xsl:apply-templates select="formula"/>
        </div>
        <xsl:apply-templates select="source"/>
        <xsl:apply-templates select="model|closer"/>
    </xsl:template>  
    
    <xsl:template match="formula">  
        <span class="formula {@sign}"><xsl:apply-templates/></span>
    </xsl:template>  
    
    <xsl:template match="llf">  
        <span class="llf"><xsl:value-of select="."/></span>
    </xsl:template>
        
    <xsl:template match="source">
        <div class="source">
        <span class="source">    
        <xsl:value-of select="@rule"/>
        <xsl:apply-templates select="idList"/>
        <xsl:if test="oldConstList">
            <xsl:text>,</xsl:text>
            <xsl:apply-templates select="oldConstList"/>
        </xsl:if>
        </span>    
        </div>
    </xsl:template>
    
    <xsl:template match="modList|argList">
            <xsl:if test="*">
                <span class="{name(.)}">
                    <xsl:for-each select="child::*[last()>position()]">
                        <xsl:value-of select="."/>
                        <xsl:text>, </xsl:text>
                    </xsl:for-each>  
                    <xsl:value-of select="child::*[last()]"/>
                </span>
            </xsl:if>     
    </xsl:template>  
  
    <xsl:template match="oldConstList|idList">
        <xsl:text>[</xsl:text>
        <xsl:for-each select="child::*[last()>position()]">
            <xsl:value-of select="."/>
            <xsl:text>,</xsl:text>
        </xsl:for-each>  
        <xsl:value-of select="child::*[last()]"/>
        <xsl:text>]</xsl:text>
    </xsl:template>
    
    <xsl:template match="model">    
        <div class="open_branch">
            <i class="fa fa-unlock"></i>
            <!--<span class="eureka"><xsl:text>Eureka!</xsl:text></span>-->
            <div><xsl:text>Open branch</xsl:text></div>
        </div>    
    </xsl:template>   
    
    <xsl:template match="closer">
        <div class="closure">
        <i class="fa fa-times-circle"></i>
        <div class="closer">
            <div class="closer_rule"><xsl:value-of select="closer_rule"/></div>
            <div class="closer_ids"><xsl:value-of select="closer_ids"/></div>
        </div>
        </div>    
    </xsl:template> 
    
</xsl:stylesheet>
