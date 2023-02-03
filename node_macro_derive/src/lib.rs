use proc_macro::TokenStream;
use quote::quote;

#[proc_macro_derive(NodeMacro)]
pub fn node_macro_derive(input: TokenStream) -> TokenStream {
    // Construct a representation of Rust code as a syntax tree
    // that we can manipulate
    let ast = syn::parse(input).unwrap();

    // Build the trait implementation
    impl_node_macro(&ast)
}

fn impl_node_macro(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let gen = quote! {
        impl Node for #name {
            fn token(&self) -> Option<&Token> {
                Some(&self.token)
            }

            fn as_any(&self) -> &dyn Any {
                self
            }
        }
    };
    gen.into()
}