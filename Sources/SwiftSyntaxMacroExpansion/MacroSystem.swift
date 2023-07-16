//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2023 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

import SwiftDiagnostics
import SwiftSyntax
@_spi(MacroExpansion) import SwiftParser
@_spi(MacroExpansion) import SwiftSyntaxMacros

/// Check if a 'DeclSyntax', 'StmtSyntax', or 'ExprSyntax' is at top level.
private func isTopLevel(node: some SyntaxProtocol) -> Bool {
  return true == node
    .parent? /* CodeBlockItem */
    .parent? /* CodeBlockItemList */
    .is(SourceFileSyntax.self).self
}

extension SyntaxProtocol {
  /// Detach the current node and inform the macro expansion context,
  /// if it needs to know.
  fileprivate func detach(in context: MacroExpansionContext) -> Self {
    if let basicContext = context as? BasicMacroExpansionContext {
      return basicContext.detach(self)
    }

    return self.detached
  }
}


private func expandFreestandingMemberDeclList(
  definition: Macro.Type,
  node: some FreestandingMacroExpansionSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> MemberDeclListSyntax? {
  guard let expanded = try expandFreestandingMacro(
    definition: definition,
    macroRole: inferFreestandingMacroRole(definition: definition),
    node: node.detach(in: context),
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  var prefix = ""
  for piece in node.leadingTrivia {
    if piece.isNewline {
      piece.write(to: &prefix)
    } else {
      break
    }
  }

  return Parser.parseExpandedMemberDeclList(
    source: prefix + expanded.applying(indentation: node.baseIndentation)
  )
}

private func expandFreestandingCodeItemList(
  definition: Macro.Type,
  node: some FreestandingMacroExpansionSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> CodeBlockItemListSyntax? {
  guard let expanded = try expandFreestandingMacro(
    definition: definition,
    macroRole: inferFreestandingMacroRole(definition: definition),
    node: node.detach(in: context),
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  var prefix = ""
  for piece in node.leadingTrivia {
    if piece.isNewline {
      piece.write(to: &prefix)
    } else {
      break
    }
  }

  return Parser.parseExpandedCodeBlockItemList(
    source: prefix + expanded.applying(indentation: node.baseIndentation),
    isAtTopLevel: isTopLevel(node: node)
  )
}

private func expandFreestandingExpr(
  definition: Macro.Type,
  node: some FreestandingMacroExpansionSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> ExprSyntax? {
  guard let expanded = expandFreestandingMacro(
    definition: definition,
    macroRole: .expression,
    node: node.detach(in: context),
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  let indented = expanded
    .applying(indentation: node.baseIndentation)
    // Remove indentation on the first line.
    .drop(while: {$0.isWhitespace})
  return "\(raw: indented)"
}

private func expandMemberMacro(
  definition: MemberMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> MemberDeclListSyntax? {
  guard let expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .member,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: attachedTo.detach(in: context),
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  var indentationStr = attachedTo.baseIndentation
  indentation.write(to: &indentationStr)

  return Parser.parseExpandedMemberDeclList(
    source: "\n\n" + expanded.applying(indentation: indentationStr)
  )
}

private func expandMemberAttributeMacro(
  definition: MemberAttributeMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo declaration: DeclSyntax,
  providingAttributeFor member: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> AttributeListSyntax? {
  guard let expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .memberAttribute,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: member.detach(in: context),
    parentDeclNode: declaration.detach(in: context),
    extendedType: nil,
    conformanceList: nil,
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  return Parser.parseExpandedAttributeList(
    source: "\n" + expanded.applying(indentation: member.baseIndentation)
  )
}

private func expandPeerMacroMember(
  definition: PeerMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> MemberDeclListSyntax? {
  guard let expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .peer,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: attachedTo.detach(in: context),
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  return Parser.parseExpandedMemberDeclList(
    source: "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  )
}

private func expandPeerMacroCodeItem(
  definition: PeerMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> CodeBlockItemListSyntax? {
  guard let expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .peer,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: attachedTo.detach(in: context),
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  return Parser.parseExpandedCodeBlockItemList(
    source: "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation),
    isAtTopLevel: isTopLevel(node: attachedTo)
  )
}

private func expandAccessorMacroWithBlock(
  definition: AccessorMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> AccessorBlockSyntax? {
  guard let expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .accessor,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: attachedTo.detach(in: context),
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  return Parser.parseExpandedAccessorBlock(
    source: "\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  )
}

private func expandAccessorMacroWithoutBlock(
  definition: AccessorMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> AccessorListSyntax? {
  guard let expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .accessor,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: attachedTo.detach(in: context),
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  return Parser.parseExpandedAccessorList(
    source: "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  )
}

private func expandExtensionMacro(
  definition: MemberMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax,
  in context: some MacroExpansionContext,
  indentation: Trivia
) throws -> CodeBlockItemListSyntax? {
  let extendedType: TypeSyntax
  if let identified = attachedTo.asProtocol(IdentifiedDeclSyntax.self) {
    extendedType = "\(identified.identifier.trimmed)"
  } else if let ext = attachedTo.as(ExtensionDeclSyntax.self) {
    extendedType = "\(ext.extendedType.trimmed)"
  } else {
    return nil
  }

  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .extension,
    attributeNode: attributeNode.detach(in: context),
    declarationNode: attachedTo.detach(in: context),
    parentDeclNode: nil,
    extendedType: extendedType.detach(in: context),
    conformanceList: [],
    in: context,
    indentation: indentation
  ) else {
    return nil
  }
  expanded = "\n\n" + expanded
  return Parser.parseExpandedCodeBlockItemList(source: expanded, isAtTopLevel: true)
}

/// Describes the kinds of errors that can occur within a macro system.
enum MacroSystemError: Error {
  /// Indicates that a macro with the given name has already been defined.
  case alreadyDefined(new: Macro.Type, existing: Macro.Type)

  /// Indicates that an unknown macro was encountered during expansion.
  case unknownMacro(name: String, node: Syntax)

  /// Indicates that a macro evaluated as an expression by the given node
  /// is not an expression macro.
  case requiresExpressionMacro(macro: Macro.Type, node: Syntax)

  /// Indicates that a macro evaluated as a code item by the given node
  /// is not suitable for code items.
  case requiresCodeItemMacro(macro: Macro.Type, node: Syntax)

  /// Indicates that a macro produced diagnostics during evaluation. The
  /// diagnostics might not specifically include errors, but will be reported
  /// nonetheless.
  case evaluationDiagnostics(node: Syntax, diagnostics: [Diagnostic])
}

private protocol WithAccessorBlock: DeclSyntaxProtocol {
  var accessorBlock: AccessorBlockSyntax? { get set }
}

extension SubscriptDeclSyntax: WithAccessorBlock {
  var accessorBlock: AccessorBlockSyntax? {
    get {
      if case .accessors(let block) = self.accessor {
        return block
      }
      return nil
    }
    set {
      if let newValue {
        accessor = .accessors(newValue)
      } else {
        accessor = nil
      }
    }
  }
}

extension VariableDeclSyntax: WithAccessorBlock {
  var accessorBlock: AccessorBlockSyntax? {
    get {
      if case .accessors(let block) = self.bindings.first?.accessor {
        return block
      }
      return nil
    }
    set {
      if !self.bindings.isEmpty {
        if  let newValue {
          bindings[bindings.startIndex].accessor = .accessors(newValue)
        } else {
          bindings[bindings.startIndex].accessor = nil
        }
      }
    }
  }
}

/// A system of known macros that can be expanded syntactically
struct MacroSystem {
  var macros: [String: Macro.Type] = [:]

  /// Create an empty macro system.
  init() {}

  /// Add a macro to the system.
  ///
  /// Throws an error if there is already a macro with this name.
  mutating func add(_ macro: Macro.Type, name: String) throws {
    if let knownMacro = macros[name] {
      throw MacroSystemError.alreadyDefined(new: macro, existing: knownMacro)
    }

    macros[name] = macro
  }

  /// Look for a macro with the given name.
  func lookup(_ macroName: String) -> Macro.Type? {
    return macros[macroName]
  }
}

/// Syntax rewriter that evaluates any macros encountered along the way.
class MacroApplication<Context: MacroExpansionContext>: SyntaxRewriter {
  let macroSystem: MacroSystem
  var context: Context
  var indentation: Trivia
  var skipNodes: Set<Syntax> = []

  /// Store expanded extension while visiting member decls. This should be
  /// added to top-level 'CodeBlockItemList'.
  var extensions: [CodeBlockItemSyntax]?

  init(
    macroSystem: MacroSystem,
    context: Context,
    indentation: Trivia
  ) {
    self.macroSystem = macroSystem
    self.context = context
    self.indentation = indentation
    super.init(viewMode: .sourceAccurate)
  }

  override func visitAny(_ node: Syntax) -> Syntax? {
    if skipNodes.contains(node) {
      return nil
    }

    // Expand 'MacroExpansionExpr'.
    // Note that 'MacroExpansionExpr'/'MacroExpansionExprDecl' at code item
    // position are handled by 'visit(_:CodeBlockItemListSyntax)'. Here's only
    // expression inside other syntax node.
    if let expanded = expandExpr(node: node) {
      return Syntax(visit(expanded))
    }

    if let declSyntax = node.as(DeclSyntax.self),
      let attributedNode = node.asProtocol(WithAttributesSyntax.self),
      let attributes = attributedNode.attributes
    {
      // Visit the node.
      skipNodes.insert(node)
      let visitedNode = self.visit(declSyntax).asProtocol(WithAttributesSyntax.self)!
      skipNodes.remove(node)

      // Remove any attached attributes.
      let newAttributes = attributes.filter {
        guard case let .attribute(attribute) = $0 else {
          return true
        }

        guard let attributeName = attribute.attributeName.as(SimpleTypeIdentifierSyntax.self)?.name.text,
          let macro = macroSystem.macros[attributeName]
        else {
          return true
        }

        return !(macro is AttachedMacro.Type)
      }

      if newAttributes.isEmpty {
        return Syntax(fromProtocol: visitedNode.with(\.attributes, nil))
      }

      return Syntax(fromProtocol: visitedNode.with(\.attributes, AttributeListSyntax(newAttributes)))
    }

    return nil
  }

  override func visit(_ node: CodeBlockItemListSyntax) -> CodeBlockItemListSyntax {
    let isAtTopLevel = node.parent?.is(SourceFileSyntax.self) == true

    var newItems: [CodeBlockItemSyntax] = []
    func addResult(_ node: CodeBlockItemSyntax) {
      // Expand freestanding macro.
      if let expanded = expandCodeBlockItem(node: node) {
        for item in expanded {
          addResult(item)
        }
        return
      }

      // Recurse on the child node
      newItems.append(visit(node))

      // Expand any peer macro on this item.
      if case .decl(let decl) = node.item {
        for peer in expandPeers(ofCodeBlockItemDecl: decl) {
          addResult(peer)
        }
      }
    }

    for item in node {
      addResult(item)
    }

    if isAtTopLevel, let extensions {
      newItems.append(contentsOf: extensions)
    }

    return CodeBlockItemListSyntax(newItems)
  }

  override func visit(_ node: MemberDeclListSyntax) -> MemberDeclListSyntax {
    let parentDeclGroup = node.parent?.parent?.as(DeclSyntax.self)
    var newItems: [MemberDeclListItemSyntax] = []

    func addResult(_ node: MemberDeclListItemSyntax) {
      // Expand freestanding macro.
      if let expanded = expandMemberDecl(node: node) {
        for item in expanded {
          addResult(item)
        }
        return
      }

      // Recurse on the child node.
      newItems.append(visit(node))

      // Expand any peer macro on this member.
      for peer in expandPeers(ofMemberDecl: node.decl) {
        addResult(peer)
      }
    }

    for var item in node {
      // Expand member attribute members attached to the declaration context.
      // Note that MemberAttribute macros are _not_ applied to generated members
      if let parentDeclGroup, item.decl.isProtocol(WithAttributesSyntax.self) {
        var newAttributes = expandAttributes(of: item.decl, parentDecl: parentDeclGroup).map {
          visit($0)
        }
        if !newAttributes.isEmpty {
          let decl = item.decl.asProtocol(WithAttributesSyntax.self)!
          if let existingAttrs = decl.attributes {
            newAttributes.insert(contentsOf: existingAttrs, at: 0)
          }
          item.decl = decl.with(\.attributes, AttributeListSyntax(newAttributes)).cast(DeclSyntax.self)
        }
      }

      // Recurse on the child node.
      addResult(item)
    }

    // Expand any member macros of parent.
    if let parentDeclGroup {
      for member in expandMembers(of: parentDeclGroup) {
        addResult(member)
      }
    }

    return .init(newItems)
  }


  override func visit(_ node: VariableDeclSyntax) -> DeclSyntax {
    let node = expandAccessors(of: node)
    return super.visit(node)
  }

  override func visit(_ node: SubscriptDeclSyntax) -> DeclSyntax {
    let node = expandAccessors(of: node)
    return super.visit(node)
  }
}

/// Attached macro expansions.
extension MacroApplication {
  /// Get pairs of a macro attribute and the macro definition attached to 'decl'
  /// matching 'ofType' macro type. The macros must be registered to
  /// 'macroSystem'.
  /// E.g.
  private func getMacroAttributes<MacroType>(
    attachedTo decl: DeclSyntax,
    ofType: MacroType.Type
  ) -> [(attributeNode: AttributeSyntax, definition: MacroType)] {
    guard let attributedNode = decl.asProtocol(WithAttributesSyntax.self),
          let attributes = attributedNode.attributes
    else {
      return []
    }

    return attributes.compactMap {
      guard case let .attribute(attribute) = $0,
        let attributeName = attribute.attributeName.as(SimpleTypeIdentifierSyntax.self)?.name.text,
        let macro = macroSystem.lookup(attributeName),
        let macroType = macro as? MacroType
      else {
        return nil
      }

      return (attribute, macroType)
    }
  }

  // If any of the custom attributes associated with the given declaration
  // refer to "peer" declaration macros, expand them and return the resulting
  // set of peer declarations.
  private func expandPeers(ofMemberDecl decl: DeclSyntax) -> [MemberDeclListItemSyntax] {
    var peers: [MemberDeclListItemSyntax] = []

    for peerMacro in getMacroAttributes(attachedTo: decl, ofType: PeerMacro.Type.self) {
      do {
        if let expanded = try expandPeerMacroMember(
          definition: peerMacro.definition,
          attributeNode: peerMacro.attributeNode,
          attachedTo: decl,
          in: context,
          indentation: indentation
        ) {
          peers.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: peerMacro.0)
      }
    }
    return peers
  }

  private func expandPeers(ofCodeBlockItemDecl decl: DeclSyntax) -> [CodeBlockItemSyntax] {
    var peers: [CodeBlockItemSyntax] = []

    for peerMacro in getMacroAttributes(attachedTo: decl, ofType: PeerMacro.Type.self) {
      do {
        if let expanded = try expandPeerMacroCodeItem(
          definition: peerMacro.definition,
          attributeNode: peerMacro.attributeNode,
          attachedTo: decl,
          in: context,
          indentation: indentation
        ) {
          peers.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: peerMacro.0)
      }
    }
    return peers
  }

  private func expandMembers(of parentDeclGroup: DeclSyntax) -> [MemberDeclListItemSyntax] {
    var members: [MemberDeclListItemSyntax] = []
    for memberMacro in getMacroAttributes(
      attachedTo: parentDeclGroup,
      ofType: MemberMacro.Type.self
    ) {
      do {
        if let expanded = try expandMemberMacro(
          definition: memberMacro.definition,
          attributeNode: memberMacro.attributeNode,
          attachedTo: parentDeclGroup,
          in: context,
          indentation: indentation
        ) {
          members.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: memberMacro.attributeNode)
      }
    }
    return members
  }

  private func expandAttributes(of decl: DeclSyntax, parentDecl: DeclSyntax) -> [AttributeListSyntax.Element] {

    var attributes: [AttributeListSyntax.Element] = []
    for memberAttributeMacro in getMacroAttributes(
      attachedTo: parentDecl,
      ofType: MemberAttributeMacro.Type.self
    ) {
      do {
        if let expanded = try expandMemberAttributeMacro(
          definition: memberAttributeMacro.definition,
          attributeNode: memberAttributeMacro.attributeNode,
          attachedTo: parentDecl,
          providingAttributeFor: decl,
          in: context,
          indentation: indentation
        ) {
          attributes.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: memberAttributeMacro.attributeNode)
      }
    }
    return attributes
  }

  private func expandAccessors<StorageNode: WithAccessorBlock>(of storage: StorageNode) -> StorageNode {
    var accessorMacros = getMacroAttributes(
      attachedTo: DeclSyntax(storage),
      ofType: AccessorMacro.Type.self
    )
    if accessorMacros.isEmpty {
      return storage
    }

    var storage = storage
    var accessorBlock = storage.accessorBlock

    NO_BLOCK: if accessorBlock == nil {
      while let macro = accessorMacros.popLast() {
        do {
          let block = try expandAccessorMacroWithBlock(
            definition: macro.definition,
            attributeNode: macro.attributeNode,
            attachedTo: DeclSyntax(storage),
            in: context,
            indentation: indentation
          )
          if let block {
            // Add the block now so the subsequence expansion doesn't add '{ ... }'.
            storage.accessorBlock = block
            break NO_BLOCK
          }
        } catch {
          context.addDiagnostics(from: error, node: macro.attributeNode)
        }
      }
    }
    if accessorBlock == nil {
      return storage
    }

    var accessors = Array(accessorBlock!.accessors)
    while let macro = accessorMacros.popLast() {
      do {
        if let expanded = try expandAccessorMacroWithoutBlock(
          definition: macro.definition,
          attributeNode: macro.attributeNode,
          attachedTo: DeclSyntax(storage),
          in: context,
          indentation: indentation
        ) {
          accessors.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: macro.attributeNode)
      }
    }
    accessorBlock!.accessors = AccessorListSyntax(accessors)
    storage.accessorBlock = accessorBlock
    return storage
  }
}

/// Freestanding macro expansion.
extension MacroApplication {
  /// Expand a freestanding macro expansion syntax in a code block item position.
  /// E.g.
  ///   function test() {
  ///     #foo
  ///   }
  func expandCodeBlockItem(node: CodeBlockItemSyntax) -> CodeBlockItemListSyntax? {
    guard let expansion = node.item.asProtocol(FreestandingMacroExpansionSyntax.self),
      let macro = macroSystem.lookup(expansion.macro.text)
    else {
      return nil
    }
    do {
      return try expandFreestandingCodeItemList(
        definition: macro,
        node: expansion,
        in: context,
        indentation: indentation
      )
    } catch {
      context.addDiagnostics(from: error, node: expansion)
      return nil
    }
  }

  /// Expand a freestanding macro expansion syntax in a member decl position.
  /// E.g.
  ///   struct S {
  ///     #foo
  ///   }
  func expandMemberDecl(node: MemberDeclListItemSyntax) -> MemberDeclListSyntax? {
    // Expand declaration macros, which produce zero or more declarations.
    guard let declExpansion = node.decl.as(MacroExpansionDeclSyntax.self),
          let macro = macroSystem.macros[declExpansion.macro.text] as? DeclarationMacro.Type else {
      return nil
    }
    do {
      return try expandFreestandingMemberDeclList(
        definition: macro,
        node: declExpansion,
        in: context,
        indentation: indentation
      )
    } catch {
      context.addDiagnostics(from: error, node: declExpansion)
      return nil
    }
  }

  /// Expand a freestanding macro expansion in a expression position inside
  /// other products. e.g.
  ///   let a = #foo
  func expandExpr(node: Syntax) -> ExprSyntax? {
    guard let expansion = node.as(MacroExpansionExprSyntax.self),
       let macro = macroSystem.lookup(expansion.macro.text)
    else {
      return nil
    }
    do {
      return try expandFreestandingExpr(
        definition: macro,
        node: expansion,
        in: context,
        indentation: indentation
      )
    } catch {
      context.addDiagnostics(from: error, node: node)
      return nil
    }
  }
}

extension DeclSyntax {
  /// Returns this node with `attributes` and `modifiers` prepended to the
  /// node’s attributes and modifiers, respectively. If the node doesn’t contain
  /// attributes or modifiers, `attributes` or `modifiers` are ignored and not
  /// applied.
  func applying(
    attributes: AttributeListSyntax?,
    modifiers: ModifierListSyntax?
  ) -> DeclSyntax {
    func _combine<C: SyntaxCollection>(_ left: C, _ right: C?) -> C? {
      guard let right = right else { return left }
      var elems: [C.Element] = []
      elems.append(contentsOf: left)
      elems.append(contentsOf: right)
      return C(elems)
    }
    var node = self
    if let attributes = attributes,
      let withAttrs = node.asProtocol(WithAttributesSyntax.self)
    {
      node = withAttrs.with(
        \.attributes,
        _combine(attributes, withAttrs.attributes)
      ).cast(DeclSyntax.self)
    }
    if let modifiers = modifiers,
      let withModifiers = node.asProtocol(WithModifiersSyntax.self)
    {
      node = withModifiers.with(
        \.modifiers,
        _combine(modifiers, withModifiers.modifiers)
      ).cast(DeclSyntax.self)
    }
    return node
  }
}

extension SyntaxProtocol {
  /// Expand all uses of the given set of macros within this syntax
  /// node.
  public func expand(
    macros: [String: Macro.Type],
    in context: some MacroExpansionContext,
    indentation: Trivia = .spaces(4)
  ) -> Syntax {
    // Build the macro system.
    var system = MacroSystem()
    for (macroName, macroType) in macros {
      try! system.add(macroType, name: macroName)
    }

    let applier = MacroApplication(
      macroSystem: system,
      context: context,
      indentation: indentation
    )

    return applier.rewrite(self)
  }
}
