export const PRESETS = [
  {
    id: "ticket",
    title: "Support ticket routing",
    kind: "choice",
    state:
      "Customer: I was charged twice for my order last week and the second charge still shows as pending on my card.",
    instructions: "Which team should handle this message?",
    options:
      "billing: payments, refunds, and charges\nshipping: delivery and tracking\naccount: login and profile changes\nother",
  },
  {
    id: "review",
    title: "Review sentiment",
    kind: "score",
    state:
      "The battery lasts two days, the screen is sharp, but the camera struggles the moment the light drops.",
    instructions: "How positive is this product review?",
    options: "very negative\nnegative\nmixed\npositive\nvery positive",
  },
  {
    id: "fact",
    title: "Fact check",
    kind: "noul",
    state: "Meeting notes: launch moved from Tuesday to Thursday; design review stays on Monday.",
    instructions: "The launch is on Thursday.",
    options: "",
  },
  {
    id: "ticket-three",
    title: "Support ticket (three questions)",
    kind: "choice",
    state: "Shoes arrived two weeks late and in the wrong size. Also I see two charges on my card.",
    instructions: "Which team should handle this?",
    options: "returns: Exchanges, refunds, wrong or damaged items\nshipping: Delivery status, delays, lost packages\nbilling: Charges, invoices, payment problems",
    extra: [
      {
        kind: "noul",
        instructions: "Does this need urgent human attention?",
        options: "",
      },
      {
        kind: "score",
        instructions: "How frustrated is the customer?",
        options: "Calm\nFrustrated\nVery angry",
      },
    ],
  },
];

export function getPreset(id) {
  return PRESETS.find((preset) => preset.id === id) ?? PRESETS[0];
}
