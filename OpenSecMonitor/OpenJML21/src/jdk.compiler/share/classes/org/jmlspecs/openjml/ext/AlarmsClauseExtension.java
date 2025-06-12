package org.jmlspecs.openjml.ext;

import static com.sun.tools.javac.parser.Tokens.TokenKind.SEMI;

import org.jmlspecs.openjml.IJmlClauseKind;
import org.jmlspecs.openjml.JmlExtension;
import org.jmlspecs.openjml.JmlTree.JmlMethodClause;

import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.TypeTag;
import com.sun.tools.javac.comp.AttrContext;
import com.sun.tools.javac.comp.Env;
import com.sun.tools.javac.comp.JmlAttr;
import com.sun.tools.javac.parser.JmlParser;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCModifiers;

public class AlarmsClauseExtension extends JmlExtension {
    
    public static final String alarmsID = "alarms";
    
    public static final IJmlClauseKind alarmsClauseKind = new IJmlClauseKind.MethodSpecClauseKind(alarmsID) {
        @Override
        public boolean oldNoLabelAllowed() { return true; }
        @Override
        public boolean preOrOldWithLabelAllowed() { return false; }

        @Override
        public JmlMethodClause parse(JCModifiers mods, String keyword, IJmlClauseKind clauseType, JmlParser parser) {
            if (mods != null) {
                error(mods, "jml.message", "A " + keyword + " clause may not have modifiers");
                return null;
            }
            
            int pp = parser.pos();
            init(parser);
            
            parser.nextToken();
            JCExpression a = parser.parseExpression();
            
            JCExpression e;
            if (parser.token().kind == SEMI) {
                e = toP(parser.maker().at(parser.pos()).Literal(TypeTag.BOOLEAN, 1)); // Boolean.TRUE));
                parser.nextToken();
            } else {
                e = parser.parseExpression();
                if (parser.token().kind != SEMI && e.getKind() != Kind.ERRONEOUS) {
                    parser.syntaxError(parser.pos(), null, "jml.missing.semi");
                    parser.skipThroughSemi();
                }
            }
            
         
            parser.nextToken();
           

            return toP(parser.maker().at(pp).JmlMethodClauseAlarms(keyword, a, clauseType, e));

        }
        
        @Override
        public Type typecheck(JmlAttr attr, JCTree expr, Env<AttrContext> env) {
            // TODO Auto-generated method stub
            return null;
        }
    };
    
}