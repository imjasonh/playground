const Button = () => (
  <button onClick={this.handleClick.bind(this)} />  // want ".bind() in JSX"
);

const Ok = (props: { onClick: () => void }) => <button onClick={props.onClick} />;
