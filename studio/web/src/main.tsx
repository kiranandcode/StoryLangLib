import React from 'react'
import { createRoot } from 'react-dom/client'
import '@fontsource-variable/literata'
import '@fontsource-variable/literata/wght-italic.css'
import '@fontsource-variable/inter'
import '@fontsource/atkinson-hyperlegible/400.css'
import '@fontsource/atkinson-hyperlegible/400-italic.css'
import './theme.css'
import './reading.css'
import './logic.css'
import './wrap.css'
import { App } from './App'

// A render error must not leave a blank window: show it, and try again when
// the story files next change (the server pushes an event) or on click.
class Boundary extends React.Component<{ children: React.ReactNode }, { error: Error | null }> {
  state = { error: null as Error | null }
  static getDerivedStateFromError(error: Error) { return { error } }
  componentDidMount() {
    try {
      const es = new EventSource('/api/events')
      es.onmessage = () => { if (this.state.error) this.setState({ error: null }) }
    } catch { /* no live stream */ }
  }
  render() {
    if (!this.state.error) return this.props.children
    return <div className="prose" style={{ padding: 24 }} onClick={() => this.setState({ error: null })}>
      <p className="para empty">The Studio hit an error drawing this story: {String(this.state.error.message)}.
        It retries when the story changes, or click to retry.</p></div>
  }
}

createRoot(document.getElementById('root')!).render(
  <React.StrictMode>
    <Boundary><App /></Boundary>
  </React.StrictMode>,
)
