import Foundation
import Tokenizers

/// Wraps a swift-transformers tokenizer loaded from the bundle's `tokenizer/`
/// folder, with the special-token ids the prompt builder needs.
struct LayaHubTokenizer: LayaTokenizing {
    private let tokenizer: Tokenizer
    let maskToken: String
    let clsTokenID: Int
    let sepTokenID: Int
    let padTokenID: Int
    let maskTokenID: Int

    init(tokenizer: Tokenizer, specialTokens: LayaSpecialTokens) throws {
        func id(_ token: String, _ name: String) throws -> Int {
            guard let id = tokenizer.convertTokenToId(token) else {
                throw LayaError.bundle("Tokenizer is missing a valid \(name)")
            }
            return id
        }
        self.tokenizer = tokenizer
        maskToken = specialTokens.mask
        clsTokenID = try id(specialTokens.cls, "cls_token")
        sepTokenID = try id(specialTokens.sep, "sep_token")
        padTokenID = try id(specialTokens.pad, "pad_token")
        maskTokenID = try id(specialTokens.mask, "mask_token")
    }

    static func load(from folder: URL, specialTokens: LayaSpecialTokens) async throws -> LayaHubTokenizer {
        let tokenizer = try await AutoTokenizer.from(modelFolder: folder)
        return try LayaHubTokenizer(tokenizer: tokenizer, specialTokens: specialTokens)
    }

    func encode(_ text: String) -> [Int] {
        tokenizer.encode(text: text, addSpecialTokens: false)
    }
}
